package dfta;

import dfta.parser.*;
import java.io.FileNotFoundException;
import java.util.HashSet;

public class FTAIncludeCheck {

   static long startTime, midTime, endTime;
   static String inputFile1, inputFile2;

   public static void main(String[] args) {
      FTAParser t1, t2;
      DeterminiserOpt det1, det2;
      String fta1, fta2;
      boolean verbose;
      verbose = false;

      try {
         for (String arg : args) {
            switch (arg) {
               case "-v":
                  verbose = true;
                  break;
            }
         }
         startTime = System.currentTimeMillis();
         // parse input
         inputFile1 = args[0];
         t1 = new FTAParser(new java.io.FileInputStream(inputFile1));
         FTAParser.FTA();
         fta1 = stripName(args[0]) + ":";

         det1 = new DeterminiserOpt(fta1, FTAParser.transitions, FTAParser.finalStates, false, false, verbose);
         det1.idx.genDelta(fta1);
         det1.idx.genFinalStates(fta1);

         inputFile2 = args[1];
         FTAParser.ReInit(new java.io.FileInputStream(inputFile2));
         FTAParser.transitions = new HashSet();
         FTAParser.finalStates = new HashSet();
         FTAParser.FTA();
         fta2 = stripName(args[1]) + ":";
         det2 = new DeterminiserOpt(fta2, FTAParser.transitions, FTAParser.finalStates, false, false, verbose);
         det2.idx.transCount = det1.idx.transCount;
         det2.idx.genDelta(fta2);
         det2.idx.genFinalStates(fta2);

         // make union of the two FTAs
         det1.idx.delta.addAll(det2.idx.delta);
         det1.idx.qs.addAll(det2.idx.qs);
         det1.idx.buildIndices();
         // for inclusion checking, set the final states of the input FTAs
         det1.q1 = det1.idx.qfs;
         det1.q2 = det2.idx.qfs;
         det1.includesCheck = true;

         midTime = System.currentTimeMillis();

         boolean b = det1.dftaStates();

         endTime = System.currentTimeMillis();
         showInput(verbose);
         if (verbose) {
            System.out.println();
            System.out.print("Result = ");
         }
         System.out.print(b + ", ");
         showTiming(verbose);

      } catch (FileNotFoundException | ParseException e) {
         System.out.println(e.getMessage());
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

   static String baseName(String f) {
      int j = f.length();
      int i = f.lastIndexOf('/');
      return f.substring(i + 1, j);
   }

   static void showInput(boolean verbose) {
      if (verbose) {
         System.out.println();
         System.out.print("Input file 1 = ");
      }
      System.out.print(baseName(inputFile1) + ", ");
      if (verbose) {
         System.out.println();
         System.out.print("Input file 2 = ");
      }
      System.out.print(baseName(inputFile2) + ", ");
   }

   static void showTiming(boolean verbose) {
      if (verbose) {
         System.out.println();
         System.out.print("File input time = ");
      }
      System.out.print((double) ((midTime - startTime) / 1000.0) + ", ");
      if (verbose) {
         System.out.println();
         System.out.print("Inclusion checking Time = ");
      }
      System.out.print((double) ((endTime - midTime) / 1000.0) + ", ");
   }

}
