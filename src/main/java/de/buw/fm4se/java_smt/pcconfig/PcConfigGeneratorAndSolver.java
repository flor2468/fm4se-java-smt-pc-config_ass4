package de.buw.fm4se.java_smt.pcconfig;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;

import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

public class PcConfigGeneratorAndSolver {

	public static void main(String[] args) throws Exception {
		
		Scanner scan = new Scanner(System.in);
		System.out.print("Please enter a budget: ");
		int budget_int = scan.nextInt();
		scan.close();
		
		
		// INFO this is just to see how to access the information from the files
		System.out.println("\nAvailable components:");
		printComponents("CPU");
		printComponents("motherboard");
		printComponents("RAM");
		printComponents("GPU");
		printComponents("storage");
		printComponents("opticalDrive");
		printComponents("cooler");
		
		System.out.println("\nConstraints:");
		printConstraints("requires");
		printConstraints("excludes");
		
		System.out.print("\nSearching for a configuration costing at most " + budget_int);
		
		// TODO implement the translation to SMT and the interpretation of the model
		// setting up SMT solver related stuff
		Configuration config = Configuration.fromCmdLineArguments(args);
		LogManager logger = BasicLogManager.create(config);
		ShutdownManager shutdown = ShutdownManager.create();

		// we use PRINCESS SMT solver as SMTINTERPOL did not support integer multiplication
		SolverContext context = SolverContextFactory.createSolverContext(config, logger, shutdown.getNotifier(),
				Solvers.PRINCESS);

		FormulaManager fmgr = context.getFormulaManager();

		IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();
		BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
		
		// declaring boolean variables for elements similar to "(declare-const ... Bool)"
		BooleanFormula i3 = bmgr.makeVariable("i3");
		BooleanFormula i7 = bmgr.makeVariable("i7");
		BooleanFormula ryzen7 = bmgr.makeVariable("ryzen7");
		
		BooleanFormula mbIntel = bmgr.makeVariable("mbIntel");
		BooleanFormula mbAMD = bmgr.makeVariable("mbAMD");
		
		BooleanFormula ram8gb = bmgr.makeVariable("ram8gb");
		BooleanFormula ram32gb = bmgr.makeVariable("ram32gb");
		BooleanFormula ram16gb = bmgr.makeVariable("ram16gb");

		BooleanFormula rtx = bmgr.makeVariable("rtx");
		BooleanFormula gtx = bmgr.makeVariable("gtx");

		BooleanFormula hdd1tb = bmgr.makeVariable("hdd1tb");
		BooleanFormula ssd2tb = bmgr.makeVariable("ssd2tb");
		BooleanFormula ssd1tb = bmgr.makeVariable("ssd1tb");
		
		BooleanFormula dvdrw = bmgr.makeVariable("dvdrw");
		
		BooleanFormula cooler = bmgr.makeVariable("cooler");
		
		// constraints
		BooleanFormula c1 = bmgr.and(bmgr.or(i3, i7, ryzen7), 
				bmgr.or(mbIntel, mbAMD), 
				bmgr.or(ram16gb, ram32gb, ram16gb), 
				bmgr.or(hdd1tb, ssd1tb, ssd2tb));
		BooleanFormula c2 = bmgr.and(bmgr.implication(bmgr.or(i3, i7),mbIntel), 
				bmgr.implication(ryzen7, mbAMD));
		
		// purpose
		// here we only encode one, e.g., office
		BooleanFormula purpose = bmgr.equivalence(dvdrw, bmgr.makeTrue());
		
		// encode rules for budget (requires integers now)
		List<IntegerFormula> costings = new ArrayList<>();
		costings.add(bmgr.ifThenElse(i3, imgr.makeNumber(113), imgr.makeNumber(0)));
		costings.add(bmgr.ifThenElse(i7, imgr.makeNumber(360), imgr.makeNumber(0)));
		costings.add(bmgr.ifThenElse(ryzen7, imgr.makeNumber(230), imgr.makeNumber(0)));
		
		costings.add(bmgr.ifThenElse(mbIntel, imgr.makeNumber(90), imgr.makeNumber(0)));
		costings.add(bmgr.ifThenElse(mbAMD, imgr.makeNumber(120), imgr.makeNumber(0)));
		
		costings.add(bmgr.ifThenElse(ram8gb, imgr.makeNumber(25), imgr.makeNumber(0)));
		costings.add(bmgr.ifThenElse(ram16gb, imgr.makeNumber(40), imgr.makeNumber(0)));
		costings.add(bmgr.ifThenElse(ram32gb, imgr.makeNumber(99), imgr.makeNumber(0)));

		costings.add(bmgr.ifThenElse(rtx, imgr.makeNumber(699), imgr.makeNumber(0)));
		costings.add(bmgr.ifThenElse(gtx, imgr.makeNumber(230), imgr.makeNumber(0)));
		
		costings.add(bmgr.ifThenElse(hdd1tb, imgr.makeNumber(39), imgr.makeNumber(0)));
		costings.add(bmgr.ifThenElse(ssd2tb, imgr.makeNumber(185), imgr.makeNumber(0)));
		costings.add(bmgr.ifThenElse(ssd1tb, imgr.makeNumber(90), imgr.makeNumber(0)));
		
		costings.add(bmgr.ifThenElse(dvdrw, imgr.makeNumber(16), imgr.makeNumber(0)));
		
		costings.add(bmgr.ifThenElse(cooler, imgr.makeNumber(40), imgr.makeNumber(0)));

		
		BooleanFormula budget = imgr.lessOrEquals(imgr.sum(costings),imgr.makeNumber(budget_int));
		
		// now feed all lines to the solver
		try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
			prover.addConstraint(c1);
			prover.addConstraint(c2);
			prover.addConstraint(purpose);
			prover.addConstraint(budget);
			
			boolean isUnsat = prover.isUnsat();
			if (!isUnsat) {
				Model model = prover.getModel();
				// print whole model
				System.out.println(model);
			} else {
				System.out.println("problem is UNSAT :-(");
			}
		}
	}

	private static void printConstraints(String kind) {
		for (String[] pair : PcConfigReader.getConstraints(kind)) {
			System.out.println(pair[0] + " " + kind + " " + pair[1]);
		}		
	}

	private static void printComponents(String type) {
		Map<String, Integer> compoents = PcConfigReader.getComponents(type);
		for (String cmp : compoents.keySet()) {
			System.out.println(cmp + " costs " + compoents.get(cmp));
		}
	}

}
