all: AudioProcessing.class
AudioProcessing.class: AudioProcessing.java
	javac -d . AudioProcessing.java
clean:
	rm -f *.class 
