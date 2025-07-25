import java.io.*;
import java.util.*;

public class LambdaEliminator {
    static Map<String, Set<String>> productions = new HashMap<>();
    static Set<String> nullable = new HashSet<>();
    static String startSymbol;
    static Set<String> terminals = new HashSet<>();
    static Set<String> variables = new HashSet<>();
    static Map<String, String> terminalVars = new HashMap<>();
    static int newVarCount = 1;

    public static void main(String[] args) throws IOException {
        Scanner sc = new Scanner(new File("input.txt"));
        PrintWriter pw = new PrintWriter("output.txt");

        int ruleCount = Integer.parseInt(sc.nextLine().trim());
        for (String t : sc.nextLine().trim().split(" "))
            if (!t.isEmpty()) terminals.add(t);

        String[] variableArr = sc.nextLine().trim().split(" ");
        for (String v : variableArr)
            if (!v.isEmpty()) variables.add(v);

        startSymbol = variableArr[0];

        for (int i = 0; i < ruleCount; i++) {
            String[] parts = sc.nextLine().trim().split("->");
            String lhs = parts[0].trim();
            String[] rhsOptions = parts[1].trim().split("\\|");

            for (String rhs : rhsOptions)
                productions.computeIfAbsent(lhs, k -> new HashSet<>()).add(rhs.trim());
        }

        String newStart = "S0";
        while (variables.contains(newStart)) newStart += "0";
        variables.add(newStart);
        productions.put(newStart, new HashSet<>(Collections.singleton(startSymbol)));
        startSymbol = newStart;

        findNullable();

        Map<String, Set<String>> newProductions = new HashMap<>();
        for (String lhs : productions.keySet()) {
            for (String rhs : productions.get(lhs)) {
                if (rhs.equals("@")) continue;
                generateCombinations(lhs, rhs, newProductions);
            }
        }

        for (String lhs : productions.keySet()) {
            for (String rhs : productions.get(lhs)) {
                if (rhs.length() == 1 && variables.contains(rhs))
                    newProductions.computeIfAbsent(lhs, k -> new HashSet<>()).add(rhs);
            }
        }

        if (nullable.contains(startSymbol)) {
            newProductions.computeIfAbsent(startSymbol, k -> new HashSet<>()).add("@");
        }

        eliminateUnitProductions(newProductions);
        removeUnreachableSymbols(newProductions, startSymbol);
        addTerminalVariables(newProductions);
        convertToBinaryProductions(newProductions);
        printProductions(newProductions, terminals, variables, startSymbol, pw);
        pw.close();
    }

    static void findNullable() {
        boolean changed;
        do {
            changed = false;
            for (String lhs : productions.keySet()) {
                for (String rhs : productions.get(lhs)) {
                    if (rhs.equals("@") || allNullable(rhs)) {
                        if (!nullable.contains(lhs)) {
                            nullable.add(lhs);
                            changed = true;
                        }
                    }
                }
            }
        } while (changed);
    }

    static boolean allNullable(String rhs) {
        for (String symbol : tokenize(rhs))
            if (!nullable.contains(symbol)) return false;
        return true;
    }

    static void generateCombinations(String lhs, String rhs, Map<String, Set<String>> newProds) {
        List<String> symbols = tokenize(rhs);
        List<Integer> nullablePos = new ArrayList<>();

        for (int i = 0; i < symbols.size(); i++)
            if (nullable.contains(symbols.get(i))) nullablePos.add(i);

        List<Set<Integer>> subsets = generateSubsets(nullablePos);
        for (Set<Integer> subset : subsets) {
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < symbols.size(); i++)
                if (!subset.contains(i)) sb.append(symbols.get(i));

            String newRhs = sb.toString();
            if (!newRhs.isEmpty() && !newRhs.equals(lhs)) {
                newProds.computeIfAbsent(lhs, k -> new HashSet<>()).add(newRhs);
            }
        }
    }

    static List<Set<Integer>> generateSubsets(List<Integer> list) {
        List<Set<Integer>> result = new ArrayList<>();
        int n = list.size();

        for (int i = 0; i < (1 << n); i++) {
            Set<Integer> subset = new HashSet<>();
            for (int j = 0; j < n; j++)
                if ((i & (1 << j)) != 0) subset.add(list.get(j));
            result.add(subset);
        }

        return result;
    }

    static List<String> tokenize(String rhs) {
        List<String> tokens = new ArrayList<>();
        int i = 0;

        while (i < rhs.length()) {
            boolean matched = false;

            for (String var : variables) {
                if (rhs.startsWith(var, i)) {
                    tokens.add(var);
                    i += var.length();
                    matched = true;
                    break;
                }
            }
            if (matched) continue;

            for (String term : terminals) {
                if (rhs.startsWith(term, i)) {
                    tokens.add(term);
                    i += term.length();
                    matched = true;
                    break;
                }
            }

            if (!matched) {
                tokens.add(rhs.substring(i, i + 1));
                i++;
            }
        }

        return tokens;
    }

    static void eliminateUnitProductions(Map<String, Set<String>> prods) {
        Map<String, Set<String>> unitClosures = new HashMap<>();

        for (String var : prods.keySet()) {
            Set<String> closure = new HashSet<>();
            closure.add(var);
            boolean changed;

            do {
                changed = false;
                Set<String> newAdditions = new HashSet<>();

                for (String v : closure) {
                    for (String rhs : prods.getOrDefault(v, Collections.emptySet())) {
                        if (rhs.length() == 1 && variables.contains(rhs))
                            if (!closure.contains(rhs)) newAdditions.add(rhs);
                    }
                }

                if (!newAdditions.isEmpty()) {
                    closure.addAll(newAdditions);
                    changed = true;
                }
            } while (changed);

            unitClosures.put(var, closure);
        }

        Map<String, Set<String>> newProds = new HashMap<>();

        for (String var : prods.keySet()) {
            Set<String> closure = unitClosures.get(var);
            Set<String> newSet = new HashSet<>();

            for (String cVar : closure) {
                for (String rhs : prods.getOrDefault(cVar, Collections.emptySet())) {
                    if (!(rhs.length() == 1 && variables.contains(rhs))) {
                        newSet.add(rhs);
                    }
                }
            }

            newProds.put(var, newSet);
        }

        prods.clear();
        prods.putAll(newProds);
    }

    static void removeUnreachableSymbols(Map<String, Set<String>> prods, String start) {
        Set<String> reachable = new HashSet<>();
        reachable.add(start);
        boolean changed;

        do {
            changed = false;
            for (String lhs : new HashSet<>(reachable)) {
                for (String rhs : prods.getOrDefault(lhs, Collections.emptySet())) {
                    for (String sym : tokenize(rhs)) {
                        if (variables.contains(sym) && reachable.add(sym)) {
                            changed = true;
                        }
                    }
                }
            }
        } while (changed);

        prods.keySet().retainAll(reachable);
        variables.retainAll(reachable);
    }

    static void addTerminalVariables(Map<String, Set<String>> prods) {
        for (String lhs : new HashSet<>(prods.keySet())) {
            Set<String> rhsSet = new HashSet<>(prods.get(lhs));
            prods.get(lhs).clear();

            for (String rhs : rhsSet) {
                List<String> symbols = tokenize(rhs);

                if (symbols.size() == 1 && terminals.contains(symbols.get(0))) {
                    prods.get(lhs).add(rhs);
                    continue;
                }

                StringBuilder newRhs = new StringBuilder();
                for (String sym : symbols) {
                    if (terminals.contains(sym)) {
                        String tVar = terminalVars.get(sym);
                        if (tVar == null) {
                            tVar = "T_" + sym;
                            while (variables.contains(tVar) || prods.containsKey(tVar)) {
                                tVar = "T" + (newVarCount++);
                            }
                            terminalVars.put(sym, tVar);
                            variables.add(tVar);
                            prods.computeIfAbsent(tVar, k -> new HashSet<>()).add(sym);
                        }
                        newRhs.append(tVar);
                    } else {
                        newRhs.append(sym);
                    }
                }

                prods.get(lhs).add(newRhs.toString());
            }
        }
    }

    static void convertToBinaryProductions(Map<String, Set<String>> prods) {
        Map<String, Set<String>> updatedProds = new HashMap<>();
        Map<String, String> combinationMap = new HashMap<>();

        for (String lhs : prods.keySet()) {
            for (String rhs : prods.get(lhs)) {
                List<String> symbols = tokenize(rhs);
                if (symbols.size() <= 2) {
                    updatedProds.computeIfAbsent(lhs, k -> new HashSet<>()).add(rhs);
                } else {
                    String prevVar = lhs;
                    for (int i = 0; i < symbols.size() - 1; i++) {
                        String first = symbols.get(i);
                        String second = symbols.get(i + 1);
                        String key = first + " " + second;

                        String newVar = combinationMap.getOrDefault(key, null);
                        if (newVar == null) {
                            newVar = "X" + (newVarCount++);
                            variables.add(newVar);
                            combinationMap.put(key, newVar);
                            updatedProds.computeIfAbsent(newVar, k -> new HashSet<>()).add(first + second);
                        }

                        if (i == symbols.size() - 2) {
                            updatedProds.computeIfAbsent(prevVar, k -> new HashSet<>()).add(newVar);
                        } else {
                            updatedProds.computeIfAbsent(prevVar, k -> new HashSet<>()).add(first + newVar);
                            prevVar = newVar;
                        }

                        i++;
                    }
                }
            }
        }

        prods.clear();
        prods.putAll(updatedProds);
    }

    static void printProductions(Map<String, Set<String>> prods, Set<String> terminals,
                                 Set<String> variables, String startSymbol, PrintWriter pw) {
        List<String> varsList = new ArrayList<>(variables);
        Collections.sort(varsList);

        List<String> varsWithRules = new ArrayList<>();
        for (String v : varsList)
            if (prods.containsKey(v)) varsWithRules.add(v);

        pw.println(varsWithRules.size());

        List<String> termsList = new ArrayList<>(terminals);
        Collections.sort(termsList);
        pw.println(String.join(" ", termsList));
        pw.println(String.join(" ", varsList));

        for (String lhs : varsWithRules) {
            List<String> rhsList = new ArrayList<>(prods.get(lhs));
            Collections.sort(rhsList);
            pw.println(lhs + " -> " + String.join(" | ", rhsList));
        }
    }
}
