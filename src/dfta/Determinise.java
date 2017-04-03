package dfta;

import dfta.parser.*;
import java.io.PrintStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.channels.FileChannel;
import java.util.Iterator;

public class Determinise {

   static long startTime, midTime, endTime;
   static String inputFile, outputFile, outputFile1;

   public static void main(String[] args) {
      FTAParser t;
      Determiniser det;
      outputFile = "output.txt";
      outputFile1 = "output.txt.txt";

      // options
      boolean help = false;
      boolean any = false;
      boolean show = false;
      boolean textbook = false;
      boolean bool = false;
      boolean dontCare = false;
      boolean outfile = false;
      boolean datalog = false;
      boolean verbose = false;
      boolean optsat = false;
      boolean sat = false;
      try {
         // decode command line arguments
         for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
               case "-help":
                  help = true;
                  break;
               case "-h":
                  help = true;
                  break;
               case "-any":
                  any = true;
                  break;
               case "-show":
                  show = true;
                  break;
               case "-text":
                  textbook = true;
                  break;
               case "-bool":
                  bool = true;
                  break;
               case "-optsat":
                  optsat = true;
                  break;
               case "-sat":
                  sat = true;
                  break;
               case "-dc":
                  dontCare = true;
                  break;
               case "-datalog":
                  datalog = true;
                  break;
               case "-v":
                  verbose = true;
                  break;
               case "-o":
                  outfile = true;
                  if (i + 1 == args.length) {
                     System.out.println("Missing output file: output written to output.txt");
                  } else {
                     outputFile = args[i + 1];
                     outputFile1 = args[i + 1]+".txt";
                  }
                  break;
            }
            if (!any) {
               dontCare = false; // ignore -dc if not computing completion
            }
         }

         if (help) {
            showHelp();
            System.exit(0);
         } else {
            inputFile = args[0];
            startTime = System.currentTimeMillis();
            // parse input
            t = new FTAParser(new java.io.FileInputStream(inputFile));
            FTAParser.FTA();

            if (textbook) {
               det = new DeterminiserTextBook(FTAParser.transitions, FTAParser.finalStates, any, verbose);
            //} else if (bool) {
            //   det = new DeterminiserDatalog(stripName(inputFile), FTAParser.transitions, FTAParser.finalStates, any);
            //} else if (sat) {
            //   det = new DeterminiserSAT("", FTAParser.transitions, FTAParser.finalStates, any, dontCare, verbose);
            //} else if (optsat) {
            //   det = new DeterminiserOptSAT("", FTAParser.transitions, FTAParser.finalStates, any, dontCare, verbose);
            } else {
               det = new DeterminiserOpt("", FTAParser.transitions, FTAParser.finalStates, any, dontCare, verbose);
            }

            midTime = System.currentTimeMillis();
            det.makeDfta();
            endTime = System.currentTimeMillis();
            showInput(verbose);
            showTiming(verbose);
            det.showStats(verbose);

            // Print result
            if (show) {
               PrintStream output, output1;
               if (outfile) {
                  output = new PrintStream(new File(outputFile));
                  output1 = new PrintStream(new File(outputFile1));
               } else {
                  output = System.out;
                  output1 = System.out;
               }
               if (datalog) {
                  det.printDftaDatalog(output);
               } else {
                  det.printDfta(output,output1);
               }
               output.close();
               output1.close();
            }
         }
      } catch (FileNotFoundException | ParseException e) {
         System.out.println(e.getMessage());
      }
   }

   static void printFinalStates(FTAParser t) {
      Iterator iter = FTAParser.finalStates.iterator();
      while (iter.hasNext()) {
         System.out.println((String) iter.next());
      }
   }

   static String stripName(String f) {
      int j = f.lastIndexOf('.');
      if (j == -1) {
         j = f.length();
      }
      int i = f.lastIndexOf('/');
      return f.substring(i + 1, j);
   }

   static void showInput(boolean verbose) {
      if (verbose) {
         System.out.println();
         System.out.print("Input file = ");
      }
      System.out.print(stripName(inputFile) + ", ");
   }

   static void showTiming(boolean verbose) {
      if (verbose) {
         System.out.println();
         System.out.print("File input time = ");
      }
      System.out.print((double) ((midTime - startTime) / 1000.0) + ", ");
      if (verbose) {
         System.out.println();
         System.out.print("Determinisation time = ");
      }
      System.out.print((double) ((endTime - midTime) / 1000.0) + ", ");
   }

   static void showHelp() {
      System.out.println("Finite Tree Automata (FTA) determinisation");
      System.out.println();
      System.out.println("Usage:");
      System.out.println("java -jar determinise.jar [-help][-h] ");
      System.out.println("java -jar determinise.jar <ftafile> [-text][-dc][-show][-any][-datalog][-o <outfile>]");
      System.out.println();
      System.out.println("-help, -h -- print this message and ignore any other arguments");
      System.out.println("-text     -- use the textbook algorithm (default is optimised algorithm)");
      System.out.println("-any      -- compute complete DFTA (default is no completion)");
      System.out.println("-dc       -- compute don't cares (default is no don't cares). Option ignored if '-any' not present. ");
      System.out.println("-show     -- display output (default is no display)");
      System.out.println("-v        -- verbose mode, printing various messages");
      System.out.println("-o <file> -- send output to file");
      System.out.println("-datalog  -- write output in Datalog format");
      System.out.println();
      System.out.println("Reference");
      System.out.println("An Optimised Algorithm for Determinisation and Completion of Finite Tree Automata.");
      System.out.println("by John P. Gallagher, Mai Ajspur and Bishoksan Kafle.");
      System.out.println("September 2014, Roskilde University Computer Science Research Report #145");
      System.out.println("Contact.  jpg@ruc.dk");
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
