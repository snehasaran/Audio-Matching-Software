
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.nio.BufferUnderflowException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.sound.sampled.AudioFileFormat;
import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.UnsupportedAudioFileException;

/*
 *  Copyright 2006-2007 Columbia University.
 *
 *  This file is part of MEAPsoft.
 *
 *  MEAPsoft is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License version 2 as
 *  published by the Free Software Foundation.
 *
 *  MEAPsoft is distributed in the hope that it will be useful, but
 *  WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with MEAPsoft; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
 *  02110-1301 USA
 *
 *  See the file "COPYING" for the text of the license.
 */
/**
 * A class for matching two audio files at a time to check
 * if there exists a 5 second match between the two and 
 * print the starting times for the same.
 * @author
 *
 */
public class AudioProcessing {

  private static String ORG_SOUND1 = null;
  private static String ORG_SOUND2 = null;
  private static final int FFT_SIZE = 1024;
  private static String FFT_LENGTH_POWER_2 = 
         "FFT length must be power of 2";
  private static int SAMPLING_FREQ = 44100;
  private static String ERROR_NOT_A_DIR = 
         "ERROR: Not a directory";
  private static String ERROR_NOT_A_FILE = 
         "ERROR: Not a file";
  private static String ERROR_DIR_EMPTY = 
         "ERROR: Empty directory";
  private static String ERROR_OUT_OF_MEM = 
         "ERROR: Result too long to read into memory";
  private static String UNSUPPORTED_FILE_FORMAT = 
         "ERROR: unsupported file format";
  private static String PRECISION = "0.0";
  private static String SLASH = "/";
  private static int ZERO = 0;
  private static int ONE = 1;
  private static int TWO = 2;
  private static int HIGH_IDEAL_FREQ = 465;
  private static int NO_OF_MISMATCH_ALLOWED = 8;
  private static int THRESHOLD_VALUE = 215;
  private static String DIR_PATH = "/course/cs5500f14/bin";
  private static String NEW_LINE = "\n";
  private static int BITS_PER_SAMPLE = 16;
  private static String NOT_PROPER_FILE = "Not a proper file";
  private static String DIR_PATH_FILES = "/tmp/subfolder/";
  private static String OUTPUT1 = "output1.wav";
  private static String OUTPUT2 = "output2.wav";
  private static String SINGLEFILE = "singleFile";
  private static String WAV_EXT = ".wav";
  private static String LEFTFILE = "leftFile";
  private static String RIGHTFILE = "rightFile";
  private static String CONVERSION_TEXT1 = "conversion_text1.txt";
  private static String CONVERSION_TEXT2 = "conversion_text2.txt";
  private static String CONVERSION_TEXT3 = "conversion_text3.txt";
  private static String MONO_MP3 = "/tmp/subfolder/MonoMp3.mp3";
  private static String OGGTOWAVFILE = 
         "/tmp/subfolder/oggtowavfirst.wav";
  private static int BYTE_BUFFER_SIZE = 4096;
  private int N, m;
  private float T,T1;

  // Lookup tables. Only need to recompute when size of FFT changes.
  double[] cos;
  double[] sin;
  double[] window;

  public AudioProcessing() {
  }
  public AudioProcessing(int N) {
    this.N = N;
    this.m = (int) (Math.log(N) / Math.log(TWO));
    // Make sure n is a power of 2
    if (N != (ONE << m)) {
      throw new RuntimeException(FFT_LENGTH_POWER_2);
    }
    // pre-compute tables
    cos = new double[N / TWO];
    sin = new double[N / TWO];
    for (int i = 0; i < N / TWO; i++) {
      cos[i] = Math.cos(-2 * Math.PI * i / N);
      sin[i] = Math.sin(-2 * Math.PI * i / N);
    }
    makeWindow();
  }
  protected void makeWindow() {
    // Make a blackman window:
    window = new double[N];
    for (int i = 0; i < window.length; i++) {
      window[i] = 
          0.42 - 0.5 * Math.cos(TWO * Math.PI * i / (N - ONE)) + 0.08
          * Math.cos(4 * Math.PI * i / (N - ONE));
    }
  }
  public double[] getWindow() {
    return window;
  }

  /**
   * *************************************************************
   * fft.c Douglas L. Jones University of Illinois at Urbana-Champaign
   * January 19, 1992 http://cnx.rice.edu/content/m12016/latest/
   *
   * fft: in-place radix-2 DIT DFT of a complex input
   *
   * input: n: length of FFT: must be a power of two
   * m: n = 2**m input/output
   * x: double array of length n with real part of data
   * y: double array of length n with imag part of data
   *
   * Permission to copy and use this program is granted as long as this
   * header is included.  
   ***************************************************************
   */
  public double fft(double[] x, double[] y) {
    int i, j, k, n1, n2, a;
    double c, s, t1, t2;
    // Bit-reverse
    j = ZERO;
    n2 = N / TWO;
    for (i = 1; i < N - ONE; i++) {
      n1 = n2;
      while (j >= n1) {
        j = j - n1;
        n1 = n1 / TWO;
      }
      j = j + n1;
      if (i < j) {
        t1 = x[i];
        x[i] = x[j];
        x[j] = t1;
        t1 = y[i];
        y[i] = y[j];
        y[j] = t1;
      }
    }
    // FFT
    n1 = ZERO;
    n2 = ONE;
    double mag[] = new double[FFT_SIZE/TWO];
    for (i = 0; i < m; i++) {
      n1 = n2;
      n2 = n2 + n2;
      a = ZERO;
      for (j = 0; j < n1; j++) {
        c = cos[a];
        s = sin[a];
        a += ONE << (m - i - ONE);
        for (k = j; k < N; k = k + n2) {
          t1 = c * x[k + n1] - s * y[k + n1];
          t2 = s * x[k + n1] + c * y[k + n1];
          x[k + n1] = x[k] - t1;
          y[k + n1] = y[k] - t2;
          x[k] = x[k] + t1;
          y[k] = y[k] + t2;

        }
      }
    }
    int halfSize = x.length/TWO;
    for (int l = 0; l < halfSize; l++) {
      mag[l] = 
          Math.abs(Math.sqrt(Math.pow(x[l], TWO) + Math.pow(y[l], TWO)));
    }
    return generateFingerprint(mag);
  }

  /**
   * Generates fingerprint for the magnitude values
   * @param mag - Double array of magnitude
   * @return - Calculated frequency
   */
  private double generateFingerprint(double[] mag) {
    double maxMagnitude = ZERO;
    int maxIndex = -1;
    for (int m = ONE; m < HIGH_IDEAL_FREQ ; m++)
    {
      if (mag[m] > maxMagnitude)
      {
        maxMagnitude = mag[m];
        maxIndex = m;
      }
    }
    double freq = maxIndex * SAMPLING_FREQ / FFT_SIZE;
    freq = ((Double)freq).hashCode();
    return freq;
  }
  
  /**
   * Main method for parsing command line arguments and 
   * calling appropriate functions accordingly.
   *
   * @param args - command line arguments
   * @throws Exception
   */
  public static void main(String[] args) throws Exception {

    File f = new File(DIR_PATH_FILES);
    if (!f.exists()) {
      f.mkdir();
    }
    ArrayList<String> arr1 = new ArrayList<String>();
    ArrayList<String> arr2 = new ArrayList<String>();
    String audio1 = null;
    String audio2 = null;
    String outputFile1 = DIR_PATH_FILES+OUTPUT1;
    String outputFile2 = DIR_PATH_FILES+OUTPUT2;

    if (args[0].equals("-d")) {
      boolean chkValue = new File(args[1]).exists();
      boolean chkPath = new File(args[1]).isDirectory();
      if (chkValue && chkPath) {
        File directory = new File(args[1] + SLASH);
        File[] fList1 = directory.listFiles();
        if (fList1.length == ZERO) {
          System.err.println(ERROR_DIR_EMPTY);
          System.exit(ONE);
        }
        else {
          for (File file : fList1) {
            if (file.isFile()) {
              arr1.add(args[1] + SLASH + file.getName());
            }
          }
        }
      }
      else {
        System.err.println(ERROR_NOT_A_DIR);
        System.exit(ONE);
      }
    }
    else {
      boolean chkValue = new File(args[1]).exists();
      boolean chkPath = new File(args[1]).isFile();
      if (chkValue && chkPath) {
        audio1 = args[1];
      }
      else {
        System.err.println(ERROR_NOT_A_FILE);
        System.exit(ONE);
      }
    }
    if (args[2].equals("-d")) {
      boolean chkValue = new File(args[3]).exists();
      boolean chkPath = new File(args[3]).isDirectory();
      if (chkValue && chkPath) {
        File directory = new File(args[3] + SLASH);
        File[] fList2 = directory.listFiles();
        if (fList2.length == ZERO) {
          System.err.println(ERROR_DIR_EMPTY);
          System.exit(ONE);
        }
        else {
          for (File file : fList2) {
            if (file.isFile()) {
              arr2.add(args[3] + SLASH + file.getName());
            }
          }
        }
      }
      else {
        System.err.println(ERROR_NOT_A_DIR);
        System.exit(ONE);
      }
    }
    else {
      boolean chkValue = new File(args[3]).exists();
      boolean chkPath = new File(args[3]).isFile();
      if (chkValue && chkPath) {
        audio2 = args[3];
      }
      else {
        System.err.println(ERROR_NOT_A_FILE);
        System.exit(ONE);
      }
    }
    String output1 = null;
    String output2 = null;
    AudioProcessing a = new AudioProcessing();
    if (arr1.size() != ZERO && arr2.size() != ZERO) {
      a.iterateOnDirectories(arr1, arr2);
    } 
    else {
      if (arr1.size() == ZERO && arr2.size() == ZERO) {
        output1 = a.correctFilePath(audio1, outputFile1);
        if (output1.equals(NOT_PROPER_FILE)) {
          System.err.println(UNSUPPORTED_FILE_FORMAT);
          System.exit(ONE);
        }
        output2 = a.correctFilePath(audio2, outputFile2);
        if (output2.equals(NOT_PROPER_FILE)) {
          System.err.println(UNSUPPORTED_FILE_FORMAT);
          System.exit(ONE);
        }
        ORG_SOUND1 = audio1;
        ORG_SOUND2 = audio2;
        a.audioProcessing(output1, output2);
      } 
      else {
        if (arr1.size() != ZERO && arr2.size() == ZERO) {
          Map<String, String> filesData = 
              new HashMap<String, String>();
          filesData = a.iterateOnSingleDirectory(arr1);
          output2 = a.correctFilePath(audio2, outputFile2);
          if (output2.equals(NOT_PROPER_FILE)) {
            System.err.println(UNSUPPORTED_FILE_FORMAT);
            System.exit(ONE);
          }
          ORG_SOUND2 = audio2;
          for (Object key : filesData.keySet()) {
            ORG_SOUND1 = key.toString().substring(ZERO,
                key.toString().length());
            a.audioProcessing(filesData.get(key), output2);
          }
        } 
        else if (arr1.size() == ZERO && arr2.size() != ZERO) {
          output1 = a.correctFilePath(audio1, outputFile1);
          if (output1.equals(NOT_PROPER_FILE)) {
            System.err.println(UNSUPPORTED_FILE_FORMAT);
            System.exit(ONE);
          }
          ORG_SOUND1 = audio1;
          Map<String, String> filesData = 
              new HashMap<String, String>();
          filesData = a.iterateOnSingleDirectory(arr2);
          for (Object key : filesData.keySet()) {
            ORG_SOUND2 = key.toString().substring(ZERO,
                key.toString().length());
            a.audioProcessing(output1, filesData.get(key));
          }
        }
      }

    }
    removeFiles(ZERO);
  }

  private static void removeFiles(int i) {
    // TODO Auto-generated method stub
    List<String> commands1 = new ArrayList<String>();
    commands1.add("rm");
    commands1.add("-r");
    commands1.add("/tmp/subfolder");
    try {
      ProcessBuilder pb1 = new ProcessBuilder(commands1);
      pb1.redirectErrorStream(true);
      Process process1 = pb1.start();
      process1.waitFor();
    } catch (Exception e) {

    }
    System.exit(i);
  }
  /**
   * Method to iterate on both directories to retrieve files
   *
   * @param arr1 - Arraylist of audio files in a directory
   * @param arr2 - Arraylist of audio files in a directory
   * @throws Exception
   */
  public void iterateOnDirectories
   (ArrayList<String> arr1, ArrayList<String> arr2) throws Exception {
    Map<String, String> files1 = new HashMap<String, String>();
    Map<String, String> files2 = new HashMap<String, String>();
    int i = ONE;
    int j = ONE;
    String output11 = null;
    String output22 = null;

    for (String temp : arr1) {
      String outputFile1 = DIR_PATH_FILES + LEFTFILE + i + WAV_EXT;
      output11 = correctFilePath(temp, outputFile1);
      if (output11.equals(NOT_PROPER_FILE)) {
        System.err.println(UNSUPPORTED_FILE_FORMAT);
        continue;
      }
      files1.put(temp, output11);
      i++;
    }
    for (String s : arr2) {
      String outputFile2 = DIR_PATH_FILES + RIGHTFILE + j + WAV_EXT;
      output22 = correctFilePath(s, outputFile2);
      if (output22.equals(NOT_PROPER_FILE)) {
        System.err.println(UNSUPPORTED_FILE_FORMAT);
        continue;
      }
      files2.put(s, output22);
      j++;
    }
    for (Object key1 : files1.keySet()) {
      for (Object key2 : files2.keySet()) {
        ORG_SOUND1 = key1.toString().substring(ZERO,
            key1.toString().length());
        ORG_SOUND2 = key2.toString().substring(ZERO,
            key2.toString().length());
        audioProcessing(files1.get(key1), files2.get(key2));
      }
    }
  }

  /**
   * Method to iterate on single directory to get files
   *
   * @param arr - Arraylist of audio files in a directory
   * @return
   * A HashMap containing the name of the audio file as key
   * and audio file name post canonical conversion.
   * @throws Exception
   */
  private Map<String, String> 
  iterateOnSingleDirectory(ArrayList<String> arr)
      throws Exception {
    Map<String, String> files1 = new HashMap<String, String>();
    int i = ONE;
    String output11 = null;
    for (String temp : arr) {
      String outputFile1 = DIR_PATH_FILES + SINGLEFILE + i + WAV_EXT;
      output11 = correctFilePath(temp, outputFile1);
      if (output11.equals(NOT_PROPER_FILE)) {
        System.err.println(UNSUPPORTED_FILE_FORMAT);
        continue;
      }
      files1.put(temp, output11);
      i++;
    }
    return files1;
  }

  /**
   * A method to obtain the real file path and correct it
   * for further processing
   * @param audioFile - Name of the audio file
   * @param outputFile - Name of the corrected audio file
   * @return - path to corrected standard canonical file
   * @throws Exception
   */
  public String correctFilePath
    (String audioFile, String outputFile) throws Exception {
    File f = new File(audioFile);
    String canonicalPath = f.getCanonicalPath();
    return checkFileFormat(canonicalPath, outputFile);
  }

  /**
   * Method to check file format
   *
   * @param audioFile - Name of the audio file
   * @param outputFile - Name of the formatted audio file
   * @return - path to formatted standard canonical file
   * @throws Exception
   */
  public String checkFileFormat(String audioFile, String outputFile)
      throws Exception {
    boolean file2 = waveCheck(audioFile);
    String outputFileReturned = null;
    if (file2 == false) {
      outputFileReturned = convertToMonoMp3(audioFile, outputFile);
      if (! (outputFileReturned.equals(NOT_PROPER_FILE))) {
        outputFileReturned = outputFile;
      }
    }
    else {
      outputFileReturned = audioFile;
    }
    return outputFileReturned;
  }

  /**
   * Checks if the audio file is a .wav file or not in 
   * standard canonical format.
   *
   * @param inputFile - Name of the audio file
   * @return - true iff the audio file is in 
   *           standard canonical form else false
   * @throws Exception
   */
  public static boolean waveCheck(String inputFile) throws Exception {
    AudioFileFormat inFileFormat;
    javax.sound.sampled.AudioFormat file;
    boolean chkWaveFile = false;
    File inCheckFile = null;
    try {
      inCheckFile = new File(inputFile);
    } catch (NullPointerException e) {

    }
    try {
      inFileFormat = AudioSystem.getAudioFileFormat(inCheckFile);
      file = inFileFormat.getFormat();
      if (inFileFormat.getType() == AudioFileFormat.Type.WAVE) {
        int channels = file.getChannels();
        int bitsPerSample = file.getSampleSizeInBits();
        float sampleRate = file.getSampleRate();
        if (AudioFormat.Encoding.PCM_SIGNED != null) {
          if (inFileFormat.getType() == AudioFileFormat.Type.WAVE)
          {
            if (channels == ONE && bitsPerSample == BITS_PER_SAMPLE
                && sampleRate == SAMPLING_FREQ) {
              chkWaveFile = true;
            }
          }
        } 
        else if (channels == TWO) {
          chkWaveFile = false;
        }
      }
    } catch (UnsupportedAudioFileException e) {
      chkWaveFile = false;
    }
    return chkWaveFile;
  }

  /**
   * Converts file to mono mp3 sampled format to get
   * to standard canonical
   * @param audio - Name of the audio file
   * @param outputFile - Name of the output file
   * @return - Name of audio file in standard canonical form
   * 
   */
  private static String 
  convertToMonoMp3(String audio, String outputFile) {
    List<String> commands = new ArrayList<String>();
    commands.add("./lame");
    commands.add("-m");
    commands.add("m");
    commands.add("--resample");
    commands.add("44.1");
    commands.add(audio);
    commands.add(MONO_MP3);
    try {
      ProcessBuilder pb = new ProcessBuilder(commands);
      pb.directory(new File(DIR_PATH));
      pb.redirectErrorStream(true);
      Process process = pb.start();
      BufferedReader reader = 
          new BufferedReader(new InputStreamReader(
              process.getInputStream()));
      FileOutputStream fos = 
          new FileOutputStream(DIR_PATH_FILES + CONVERSION_TEXT1);
      fos.flush();
      BufferedWriter bw = 
          new BufferedWriter(new OutputStreamWriter(fos));
      String line;
      while ((line = reader.readLine()) != null) {
        bw.write(line + NEW_LINE);
      }
      bw.close();
      process.waitFor();
      int value = process.exitValue();
      if (value == ONE) {
        return convertFromOggToWav(audio, outputFile);
      }
    } catch (Exception e) {

    }
    String newMp3 = MONO_MP3;
    String fileToReturnWav = convertToMonoWav(newMp3, outputFile);
    return fileToReturnWav;
  }

  /**
   * Converts mono MP3 file to mono wav file
   *
   * @param audioNewMp3 - Mono and resampled .mp3 audio file
   * @param outputFile - Name of the output file
   * @return - Name of audio file in standard canonical form
   */
  private static String convertToMonoWav
  (String audioNewMp3, String outputFile) {
    List<String> commands = new ArrayList<String>();
    commands.add("./lame");
    commands.add("--decode");
    commands.add(audioNewMp3);
    commands.add(outputFile);
    try {
      ProcessBuilder pb = new ProcessBuilder(commands);
      pb.directory(new File(DIR_PATH));
      pb.redirectErrorStream(true);
      Process process = pb.start();
      BufferedReader reader = 
          new BufferedReader(new InputStreamReader(
              process.getInputStream()));
      FileOutputStream fos = 
          new FileOutputStream
          (DIR_PATH_FILES + CONVERSION_TEXT2);
      fos.flush();
      BufferedWriter bw = new BufferedWriter
          (new OutputStreamWriter(fos));
      String line;
      while ((line = reader.readLine()) != null) {
        bw.write(line + NEW_LINE);
      }
      bw.close();
      process.waitFor();
    } catch (Exception e) {
    }
    String newWav = outputFile;
    String fileReturedAfterBitwidth = 
        convertToBitwidth(newWav, outputFile);
    return fileReturedAfterBitwidth;
  }

  /**
   * Converts .ogg file to .wav file for further processing
   * @param audio - Name of the input audio file
   * @param outputFile - Name of the output file
   * @return - Name of audio file in standard canonical form
   */
  public static String convertFromOggToWav
    (String audio, String outputFile) {
    String wavOutput = OGGTOWAVFILE;
    List<String> commands = new ArrayList<String>();
    commands.add("oggdec");
    commands.add("--output=" + wavOutput);
    commands.add(audio);    
    try {
      ProcessBuilder pb = new ProcessBuilder(commands);
      pb.directory(new File(DIR_PATH));
      pb.redirectErrorStream(true);
      Process process = pb.start();
      BufferedReader reader = 
          new BufferedReader(new InputStreamReader(
              process.getInputStream()));
      FileOutputStream fos = 
          new FileOutputStream(DIR_PATH_FILES + CONVERSION_TEXT3);
      fos.flush();
      BufferedWriter bw = 
          new BufferedWriter(new OutputStreamWriter(fos));
      String line;
      while ((line = reader.readLine()) != null) {
        bw.write(line + NEW_LINE);
      }
      bw.close();
      process.waitFor();
      int val = process.exitValue();
      if (val == ONE) {
        return NOT_PROPER_FILE;
      }
    } catch (Exception e) {

    }
    String newWav = wavOutput;
    String fileToReturnWav = convertToMonoMp3(newWav, outputFile);
    return fileToReturnWav;
  }

  /**
   * Sets the bit width to 16 bits for standard canonical
   *
   * @param newWav - .wav file which is resampled and mono in nature
   * @param outputFile - Name of the output file produced
   * @return - Name of audio file in standard canonical form
   */
  public static String convertToBitwidth
  (String newWav, String outputFile) {
    List<String> commands = new ArrayList<String>();
    commands.add("./wav");
    commands.add("--bitwidth");
    commands.add("16");
    commands.add(newWav);
    commands.add(outputFile);
    try {
      ProcessBuilder pb = new ProcessBuilder(commands);
      pb.directory(new File(DIR_PATH));
      pb.redirectErrorStream(true);
      Process process = pb.start();
      process.waitFor();
    } catch (Exception e) {

    }
    String finalWav = outputFile;
    String fileReturedAfterBitwidth = 
        convertToStdCanonicalWav(finalWav,outputFile);
    return fileReturedAfterBitwidth;
  }

  /**
   * Converts to standard and final .wav r
   * file for FFT processing and furthe comparison.
   *
   * @param finalWav - Name of the .wav file post resampling, 
   * downmixing and setting bit width to 16 bits
   * @param outputFile - Name of the output file
   * @return - Name of audio file in standard canonical form
   */
  public static String convertToStdCanonicalWav(String finalWav,
      String outputFile) {
    List<String> commands = new ArrayList<String>();
    commands.add("./wav");
    commands.add("--copy");
    commands.add(finalWav);
    commands.add(outputFile);
    try {
      ProcessBuilder pb = new ProcessBuilder(commands);
      pb.directory(new File(DIR_PATH));
      pb.redirectErrorStream(true);
      Process process = pb.start();
      process.waitFor();
    } catch (Exception e) {

    }
    String fileReturedAfterBitwidth = outputFile;
    return fileReturedAfterBitwidth;
  }

  /**
   * A method to process the audio files by reading it,
   * creating chunks, performing fft and then comparing the
   * fingerprints obtained
   *
   * @param soundFile1 - First audio file
   * @param soundFile2 - Second audio file
   * @throws IOException
   */
  public void audioProcessing(String soundFile1, String soundFile2) 
      throws IOException {
    int N = FFT_SIZE;
    AudioProcessing fft = new AudioProcessing(N);
    ArrayList<Double> audio1Data = null;
    ArrayList<Double> audio2Data = null;
    try {
      File soundFile = new File(soundFile1);
      AudioInputStream audioInputStream = AudioSystem
          .getAudioInputStream(soundFile);
      AudioFormat audioFormat1 = audioInputStream.getFormat();
      T = audioInputStream.getFrameLength()
          / audioFormat1.getFrameRate();
      Double[] x1 = fft.readData(soundFile1);
      audio1Data = createChunks(x1, N);
      File soundFileToCompare = new File(soundFile2);
      AudioInputStream audioInputStream1 = AudioSystem
          .getAudioInputStream(soundFileToCompare);
      AudioFormat audioFormat2 = audioInputStream1.getFormat();
      T1 = audioInputStream1.getFrameLength()
          / audioFormat2.getFrameRate();
      Double[] x2 = fft.readData(soundFile2);
      audio2Data = createChunks(x2, N);
      int m = audio1Data.size();
      int n = audio2Data.size();
      matchFingerprint(audio1Data, audio2Data, m, n);
    }
    catch (OutOfMemoryError e){
      System.err.println(ERROR_OUT_OF_MEM);
    }
    catch (IOException e) {

    }
    catch (Exception e) {
    }

  }

  /**
   * Creates chunks of FFT size = 1024 for FFT processing
   *
   * @param x2 - Raw data read from audio file in double array
   * @param N - FFT size
   * @return - Frequency of audio file in human hearing range.
   */
  public static ArrayList<Double> createChunks(Double[] x2, int N) {
    double[] re = new double[N];
    double[] im = new double[N];
    double result = ZERO;
    ArrayList<Double> freqResult = new ArrayList<Double>();
    AudioProcessing fft = new AudioProcessing(N);
    int newLength = x2.length;
    int rem = ZERO;
    int divisor = FFT_SIZE;
    rem = newLength % divisor;
    int d = divisor - rem;
    newLength = newLength + d;
    double[] data = new double[newLength];
    for (int n = 0; n < newLength; n++) {
      if (n < x2.length) {
        data[n] = x2[n];
      } else {
        data[n] = 0.0;
      }
    }
    int dataIndex = ZERO;
    int numberOfChunks = newLength / FFT_SIZE;
    for (int i = 0; i < numberOfChunks; i++) {
      for (int j = 0; j < N; j++) {
        im[j] = ZERO;
        re[j] = (data[dataIndex]);
        dataIndex++;
      }
      result = fft.fft(re, im);
      freqResult.add(result);
    }
    return freqResult;
  }


  /**
   * Reads data from audio file and converts it to double array.
   *
   * @param audio - Name of the audio file to be read
   * @return - Double array of the data read
   * @throws IOException
   */
  public Double[] readData(String audio) throws IOException {
    AudioInputStream audioInputStream = null;
    File soundFile = new File(audio);
    try {
      audioInputStream = AudioSystem.getAudioInputStream(soundFile);
    } catch (Exception e) {
    }
    final ByteArrayOutputStream bout = new ByteArrayOutputStream();
    byte[] abData = null;
    byte[] buffer = new byte[BYTE_BUFFER_SIZE];
    int c;
    while ((c =
         audioInputStream.read(buffer, ZERO, buffer.length)) != -1)
    {
      bout.write(buffer, ZERO, c);
    }
    abData = bout.toByteArray();
    audioInputStream.close();
    bout.close();
    Double[] list = new Double[abData.length / TWO];
    int p = ZERO;
    byte[] a = new byte[TWO];
    @SuppressWarnings("unused")
    int newCount = ZERO;
    try {
      for (int l = 0; l < abData.length - ONE; l += TWO) {
        a[0] = abData[l];
        a[1] = abData[l + 1];
        ByteBuffer b = ByteBuffer.wrap(a)
            .order(ByteOrder.LITTLE_ENDIAN);
        int convertedValue = b.getShort();
        list[p] = (double) convertedValue;
        newCount += ONE;
        p++;
      }
    } catch (BufferUnderflowException bufe) {
    }
    return list;
  }

  /**
   * A method to match the frequency fingerprints
   * @param audio1Data - Arraylist containing the hash of the 
   * frequencies for first audio file.
   * @param audio2Data - Arraylist containing the hash of the 
   * frequencies for second audio file.
   * @param m - Size of audio1Data
   * @param n - Size of audio2Data
   */
  private void matchFingerprint(ArrayList<Double> audio1Data,
      ArrayList<Double> audio2Data, int m, int n) {
    int maxGreat = Integer.MIN_VALUE;
    String[] array1 = ORG_SOUND1.split(SLASH);
    String[] array2 = ORG_SOUND2.split(SLASH);
    int x = ZERO, y = ZERO;
    int xMax =Integer.MIN_VALUE, yMax = Integer.MIN_VALUE;
    for ( int  i = 0; i < m; i++){
      int maxCount = ZERO;
      int ind = i;
      int jIndex = ZERO;
      int threshold = ZERO;
      boolean flag=true;
      int maxCount1 = Integer.MIN_VALUE;
      boolean flag1 = true;
      int jIndUnmatched = ZERO;
      for (int j = 0; j < n && ind < m;j++){
        if(flag1){
          jIndUnmatched = j;
          flag1= false;
        }
        if(audio1Data.get(ind).equals(audio2Data.get(j))){
          if(flag){
            jIndex = j;
            flag=false;
          }
          maxCount = maxCount + ONE;
          ind++;
          threshold = ZERO;
          if(j == n - ONE)
          {
            maxCount1 = maxCount;
            xMax = i;
            yMax = j = jIndex;
          }
          if(maxCount1 < maxCount){
            maxCount1 = maxCount;
            xMax = i;
            yMax = jIndex;
          }
        }
        else{
          threshold++;
          if (threshold > NO_OF_MISMATCH_ALLOWED){
            if(!flag){
              if(maxCount1 < maxCount){
                maxCount1 = maxCount;
                xMax = i;
                yMax = jIndex;
              }
              j = jIndex;
              flag = true;
              maxCount = ZERO;
            }
            threshold = ZERO;
            ind = i;
            if(!flag1 && flag){
              j = jIndUnmatched;
              flag1 = true;
            }
          }
          else
            ind++;
        }
      }

      if(maxGreat < maxCount1){
        maxGreat = maxCount1;
        x = xMax;
        y = yMax;
      }
    }
    DecimalFormat form = new DecimalFormat(PRECISION);
    float xTime = x * T / m;
    float yTime = y * T1 / n;
    if (xTime < (T - 2.5) && yTime < (T1 - 2.5)) {
      if (maxGreat >= THRESHOLD_VALUE) {
        System.out.println("MATCH " + array1[array1.length-ONE] 
          + " " + array2[array2.length -ONE] + " " + form.format(xTime)
          + " " + form.format(yTime));
      }
    }
  }
}
