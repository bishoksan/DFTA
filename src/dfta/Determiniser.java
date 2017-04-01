package dfta;

import java.io.PrintStream;

interface Determiniser {

   public Indices getIdx();

   public void makeDfta();

   public void printDfta(PrintStream output,PrintStream output1);

   public void printDftaDatalog(PrintStream output);

   public void showStats(boolean verbose);

   public boolean includes(String q1, String q2);
}
