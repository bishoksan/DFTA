package dfta;

import dfta.parser.*;
import dfta.parser.syntaxtree.*;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.nio.channels.FileChannel;
import java.util.Iterator;
import javax.swing.JTextArea;


public class Determinise {

    static long startTime, midTime, endTime;

    public static void main(String[] args) {
        FTAParser t;
        Determiniser det;
        String outputFile = "output.txt";
        boolean any = false;
        boolean show = false;
        boolean textbook = false;
        boolean dontCare = true;
        boolean outfile = false;
        boolean interactive = false;
        try { 
            // decode command line arguments
            for (int i=1; i<args.length; i++) {
            	if (args[i].equals("-any")) any = true;
            	else 
            	if (args[i].equals("-show")) show = true;
            	else 
            	if (args[i].equals("-text")) textbook = true;
            	else 
            	if (args[i].equals("-nodc")) dontCare = false;
            	else 
            	if (args[i].equals("-o")) {
            		outfile = true;
            		if (i+1 == args.length) 
            			System.out.println("Missing output file: output written to output.txt");
            		else
            			outputFile = args[i+1];
            	}
            	else
            	if (args[i].equals("-i")) interactive = true;		
            }
            startTime = System.currentTimeMillis();
            // parse input
            t = new FTAParser(new java.io.FileInputStream(args[0]));
            t.FTA();
            // printFinalStates(t);
           


            if (textbook) 
            	det = new DeterminiserTextBook(t.transitions,t.finalStates,any);
            else
            	det = new DeterminiserOpt("",t.transitions,t.finalStates,any,dontCare);

            midTime = System.currentTimeMillis();
            det.makeDfta();
            endTime = System.currentTimeMillis();

            showTiming();
            //det.showStats( );
            if (show) {
            	PrintStream output;
            	if (outfile)
            		output = new PrintStream(new File(outputFile));
            	else
            		output = System.out;
            	det.printDfta(output);
            	output.close();
            }
            if (interactive) {
            	BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
            	String q1 = " ";
            	String q2 = " ";
            	System.out.println("Enter states to be checked for inclusion (q1 includes q2):");
            	System.out.println("Terminate with empty string");
            	while (true) {
            		try {
            			System.out.print("q1 = ");
         				q1 = br.readLine();
         				if (q1.equals("")) break;
         				System.out.print("q2 = ");
         				q2 = br.readLine();
      					} 
      				catch (IOException e) {
         				System.out.println("IO error trying to read state names");
         				System.exit(1);
      				}
      				if (!det.getIdx().qs.contains(q1)) 
      					System.out.println(q1 + " not a valid state");
      				else
      				if (!det.getIdx().qs.contains(q2)) 
      					System.out.println(q2 + " not a valid state");
      				else
      					System.out.println(det.includes(q1,q2));
      				System.out.println();
      			}
            }
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
        }
    }

	static void printFinalStates(FTAParser t) {
        Iterator iter = t.finalStates.iterator();
        while (iter.hasNext()) {
            System.out.println((String) iter.next());
        }
    }
	
	static String stripName(String f) {
		int j = f.lastIndexOf('.');
		if (j== -1) j = f.length();
		int i = f.lastIndexOf('/');
        return f.substring(i+1,j);
	}
	
    static void showTiming() {
        System.out.println("=======================");
        System.out.println("Input Time: " + (double)((midTime - startTime) / 1000.0) + " seconds");
        System.out.println("DFTA generation Time: " + (double)((endTime - midTime) / 1000.0) + " seconds");
        System.out.println("=======================");
    }
    
    public static void copyFile(File sourceFile, File destFile) throws IOException {
    if(!destFile.exists()) {
        destFile.createNewFile();
    }

    FileChannel source = null;
    FileChannel destination = null;

    try {
        source = new FileInputStream(sourceFile).getChannel();
        destination = new FileOutputStream(destFile).getChannel();
        destination.transferFrom(source, 0, source.size());
    }
    finally {
        if(source != null) {
            source.close();
        }
        if(destination != null) {
            destination.close();
        }
    }
}

}