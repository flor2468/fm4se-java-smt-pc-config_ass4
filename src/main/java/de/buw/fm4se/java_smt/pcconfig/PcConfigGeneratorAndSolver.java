package de.buw.fm4se.java_smt.pcconfig;

import java.util.*;

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

        System.out.println("\nSearching for a configuration costing at most " + budget_int);

        // TODO implement the translation to SMT and the interpretation of the model

        List<String> components_string = new ArrayList<String>(Arrays.asList("CPU", "motherboard", "RAM", "GPU", "storage", "opticalDrive", "cooler"));


        // setting up SMT solver related stuff
        Configuration config = Configuration.fromCmdLineArguments(args);
        LogManager logger = BasicLogManager.create(config);
        ShutdownManager shutdown = ShutdownManager.create();

        // we use PRINCESS SMT solver as SMTINTERPOL did not support integer multiplication
        SolverContext context = SolverContextFactory.createSolverContext(config, logger, shutdown.getNotifier(),
                Solvers.PRINCESS);

        FormulaManager fmgr = context.getFormulaManager();
        Map<String, BooleanFormula> booleanFormulaMap = new HashMap<>();
        BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
        IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();

        Map<String, Map<String, Integer>> components = new HashMap<>();

        // encode rules for budget (requires integers now)
        List<IntegerFormula> costings = new ArrayList<>();

        for (int i = 0; i < components_string.size(); ++i) {

            Map<String, Integer> new_components = PcConfigReader.getComponents(components_string.get(i));

            for (Map.Entry<String, Integer> entry : new_components.entrySet()) {
                // declaring boolean variables for elements similar to "(declare-const ... Bool)"
                booleanFormulaMap.put(entry.getKey(), bmgr.makeVariable(entry.getKey()));
                //System.out.println("Component: " + entry.getKey() + " Price: " + new_components.get(entry.getKey()));
                // encode rules for budget (requires integers now)
                costings.add(bmgr.ifThenElse(booleanFormulaMap.get(entry.getKey()), imgr.makeNumber(new_components.get(entry.getKey())), imgr.makeNumber(0)));
            }
            components.put(components_string.get(i), new_components);
        }


        // purpose
        // here we only encode one, e.g., office
        //BooleanFormula purpose = bmgr.equivalence(booleanFormulaMap.get("dvdrw"), bmgr.makeTrue());
        BooleanFormula purpose = bmgr.equivalence(booleanFormulaMap.get("RTX"), bmgr.makeTrue());

        BooleanFormula budget = imgr.lessOrEquals(imgr.sum(costings), imgr.makeNumber(budget_int));

        // now feed all lines to the solver
        try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {


            /*/
            BooleanFormula c1 = bmgr.and(
                    bmgr.or(i3, i7, ryzen7),
                    bmgr.or(mbIntel, mbAMD),
                    bmgr.or(ram16gb, ram32gb, ram16gb),
                    bmgr.or(hdd1tb, ssd1tb, ssd2tb));
            /**/
            List<String> components_constraint = new ArrayList<String>(Arrays.asList("CPU", "motherboard", "RAM", "storage"));
            BooleanFormula and = bmgr.makeTrue();
            for (int i = 0; i < components_constraint.size(); ++i) {

                BooleanFormula or = bmgr.makeFalse();

                for (Map.Entry<String, Integer> entry : components.get(components_constraint.get(i)).entrySet()) {
                    or = bmgr.or(or, booleanFormulaMap.get(entry.getKey()));
                }
                and = bmgr.and(and, or);
            }

            prover.addConstraint(and);

            List<String[]> constraint_requires = PcConfigReader.getConstraints("requires");
            for (int i = 0; i < constraint_requires.size(); ++i) {

                //BooleanFormula c2 = bmgr.and(bmgr.implication(bmgr.or(i3, i7), mbIntel),
                //        bmgr.implication(ryzen7, mbAMD));
                // i3 or iz -> intel & ryzen -> AMD

                BooleanFormula a = booleanFormulaMap.get(constraint_requires.get(i)[0]);
                BooleanFormula b = booleanFormulaMap.get(constraint_requires.get(i)[1]);

                prover.addConstraint(bmgr.implication(a, b));
            }

            List<String[]> constraint_excludes = PcConfigReader.getConstraints("excludes");
            for (int i = 0; i < constraint_excludes.size(); ++i) {

                BooleanFormula a = booleanFormulaMap.get(constraint_excludes.get(i)[0]);
                BooleanFormula b = booleanFormulaMap.get(constraint_excludes.get(i)[1]);

                prover.addConstraint(bmgr.implication(a, bmgr.not(b)));
            }

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
