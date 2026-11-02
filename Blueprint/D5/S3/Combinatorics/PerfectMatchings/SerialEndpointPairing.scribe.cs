using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class SerialEndpointPairingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/SerialEndpointPairing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual first-return pairings of arbitrary finite modules compose in series on the full original carrier.",
        H("Serial Composition of Actual Endpoint Pairings"),
        Blocks(
            Describe.Lean(DescribeId.Create("two-permutation-forms"),
                DeclarationHandle.Create(Prefix + "two_forms"),
                H("The two permutations of two points"),
                StatementSource.FromAuthor(Disp(All("c", Call("Perm", Fin(Num(2))),
                    new Formula.Logic(Equal(V("c"), Num(1)), FormulaLogicOperator.Or,
                        Equal(V("c"), Call("swap", Num(0), Num(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every permutation of Fin(2) is either the identity or the swap of 0 and 1."))),
                DescribeRole.Theorem),
            Paragraph(Text("A cut module consists of a finite carrier X, an involutive corner permutation s "
                + "with no fixed point, an involutive band permutation r, and an equivalence e from Fin(4) "
                + "onto the entire fixed set of r. The labels 0 and 1 are the left pair, and 2 and 3 the right pair. "
                + "The local pairing is e inverse composed with endpointPairing(s,r) composed with e. "
                + "Here endpointPairing is the actual first positive return of s*r to Fix(r), not an additional input. "
                + "Its involutivity and absence of fixed points imply the three forms D=(01)(23), "
                + "T=(02)(13), and U=(03)(12). A pairing is through when it differs from D.")),
            Paragraph(Text("Let n be any natural number. The family M has n+1 cut modules indexed by Fin(n+1), "
                + "and c assigns an arbitrary permutation of Fin(2) to each of the n adjacent connectors. "
                + "Put L(i,a)=e_i(a) and R(i,a)=e_i(2+a), for a in Fin(2). "
                + "The chain carrier is the full disjoint union of the original X_i, with flags written (i,x). "
                + "Its corner action is the original s_i on each summand. Its band action preserves r_i away from "
                + "the local ports, joins (i,R(i,a)) with (i+1,L(i+1,c_i(a))), and fixes the two flags at "
                + "the first left port and the two at the last right port. These prescriptions define an involution: "
                + "the connector pairs are disjoint, every local nonport pair is retained, and the four outer flags "
                + "are exactly the fixed points. In serialOn(n,M,c), the outer equivalence lists these flags in "
                + "the order first-left 0, first-left 1, last-right 0, last-right 1. The global corner has no fixed point.")),
            Describe.Lean(DescribeId.Create("serial-actual-pairing"),
                DeclarationHandle.Create(Prefix + "serial_endpoint_pairing"),
                H("The Original-Carrier Serial Criterion and its Action Laws"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the displayed formula K(n,M,c) denotes serialOn(n,M,c), "
                        + "P denotes the actual labelled endpoint pairing, and Dead denotes D. "
                        + "The six conjuncts give the corner action, the nonport band action, every forward "
                        + "connector pair, the two left outer labels, the two right outer labels, and the through criterion. "
                        + "The reverse connector action follows from band involutivity. The type of K also includes "
                        + "the finite carrier, involutivity of both actions, the free-corner law, and the exact "
                        + "outer-port equivalence. The case n=0 is one original module with no connector.")),
                    Paragraph(Text("First consider two modules. Their disjoint-union corner and cut-band actions "
                        + "have eight exposed flags. An iterate starting in either summand remains there until "
                        + "reattachment, so its first-return time and endpoint are precisely those of that original module. "
                        + "Thus the actual eight-port pairing is the disjoint sum of the two local pairings. "
                        + "Reattaching the two adjacent pairs changes the orbit relation on these eight flags "
                        + "to the orbit relation of the actual local-pairing sum followed by the connector. "
                        + "This is the original endpoint-pairing reattachment theorem, applied to the constructed cut.")),
                    Paragraph(Text("For any four-port cut module, the two left labels are in the same corner/band "
                        + "rotation orbit exactly when its actual pairing is D. Apply this observation to the two-module "
                        + "chain. The three structural forms of each local pairing and the two permutations of Fin(2) "
                        + "show that the two outer left labels are in different rotation orbits exactly when both local "
                        + "pairings are through. Induction, attaching the final module to the existing chain, proves "
                        + "the assertion for every length. The explicit equivalence with the tagged original carrier "
                        + "transports the original corner and band actions and all four outer labels.")),
                    Paragraph(Text("No connectedness or restriction on unmarked components is imposed. "
                        + "The construction keeps components missing all local ports and closed components meeting "
                        + "internal ports but missing the four outer ports. They do not change the marked orbit "
                        + "relations used above. This result is the deterministic series rule; it makes no assertion "
                        + "about diamond counts, sign distributions, physical edge categories, necklace graph "
                        + "properties, expected values, thresholds or limits."))),
                DescribeRole.Theorem))));

    private static Formula V(string x) => F.Id(x);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Indices() => Fin(Add(V("n"), Num(1)));
    private static Formula Module(Formula i) => Call("apply", V("M"), i);
    private static Formula X(Formula i) => Call("Carrier", Module(i));
    private static Formula K() => Call("serialOn", V("n"), V("M"), V("c"));
    private static Formula Flag(Formula i, Formula x) => Call("pair", i, x);
    private static Formula Left(Formula i, Formula a) => Call("ports", Module(i), Call("castAdd", a, Num(2)));
    private static Formula Right(Formula i, Formula a) => Call("ports", Module(i), Call("natAdd", a, Num(2)));
    private static Formula Band(Formula x) => Call("band", K(), x);
    private static Formula P(Formula m) => Call("pairing", m);
    private static Formula Dead() => Call("Dead");

    private static Formula Statement()
    {
        var i = V("i");
        var x = V("x");
        var a = V("a");
        var j = Call("castSucc", i);
        var next = Call("succ", i);
        var ca = Call("apply", Call("apply", V("c"), i), a);
        var corners = All("i", Indices(), All("x", X(i),
            Equal(Call("corner", K(), Flag(i, x)), Flag(i, Call("corner", Module(i), x)))));
        var interior = All("i", Indices(), All("x", X(i),
            Imp(NotEqual(Call("band", Module(i), x), x),
                Equal(Band(Flag(i, x)), Flag(i, Call("band", Module(i), x))))));
        var connectors = All("i", Fin(V("n")), All("a", Fin(Num(2)),
            Equal(Band(Flag(j, Right(j, a))), Flag(next, Left(next, ca)))));
        var outerLeft = All("a", Fin(Num(2)),
            Equal(Call("ports", K(), Call("castAdd", a, Num(2))), Flag(Num(0), Left(Num(0), a))));
        var last = Call("last", V("n"));
        var outerRight = All("a", Fin(Num(2)),
            Equal(Call("ports", K(), Call("natAdd", a, Num(2))), Flag(last, Right(last, a))));
        var through = Iff(NotEqual(P(K()), Dead()),
            All("i", Indices(), NotEqual(P(Module(i)), Dead())));
        return Disp(All("n", V("Nat"),
            All("M", Call("Function", Indices(), V("CutModule")),
            All("c", Call("Function", Fin(V("n")), Call("Perm", Fin(Num(2)))),
                And(corners, And(interior, And(connectors, And(outerLeft, And(outerRight, through)))))))));
    }
}
