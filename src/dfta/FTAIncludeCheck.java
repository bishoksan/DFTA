package dfta;

import dfta.parser.*;
import java.io.PrintStream;
import java.io.File;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.IOException;
import java.util.LinkedHashSet;

public class FTAIncludeCheck {

    static long startTime, midTime, endTime;

    public static void main(String[] args) {
        FTAParser t1,t2;
        DeterminiserOpt det1, det2;
        String fta1, fta2;
       
        try { 
            startTime = System.currentTimeMillis();
            // parse input
            t1 = new FTAParser(new java.io.FileInputStream(args[0]));
            t1.FTA();
			fta1 = stripName(args[0])+":";
			
            det1 = new DeterminiserOpt(fta1,t1.transitions,t1.finalStates,false,false);
            det1.idx.genDelta(fta1);
            det1.idx.genFinalStates(fta1);
            

			t1.ReInit(new java.io.FileInputStream(args[1]));
			t1.transitions = new LinkedHashSet();
			t1.finalStates = new LinkedHashSet();
            t1.FTA();
            fta2 = stripName(args[1])+":";
            det2 = new DeterminiserOpt(fta2,t1.transitions,t1.finalStates,false,false);
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
            
            //boolean b = det1.inclusionCheck(det1.idx.qfs,det2.idx.qfs);
            endTime = System.currentTimeMillis();

            System.out.println("==============");
            System.out.println("Result: " + b);
            showTiming();
            System.out.println("Number of input FTA states = " + det1.idx.qs.size());
			System.out.println("Number of input FTA transitions = " + det1.idx.delta.size());
			System.out.println("=============================================");
            
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
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
        System.out.println("Inclusion checking Time: " + (double)((endTime - midTime) / 1000.0) + " seconds");
        System.out.println("=======================");
    }

}
