using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class IncomingLiftAmbiguityCriterionDocument : IScribeDocumentDefinition
{
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Some(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Twice(Formula value) =>
        new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, value);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original-edge code of a finite incoming lift is classified by unordered fiber ambiguity.",
        H("Exact memory and bounded periodic collisions"),
        Blocks(Describe.Lean(
            DescribeId.Create("incoming-lift-ambiguity-criterion"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/IncomingLiftAmbiguityCriterion.incoming_lift_ambiguity_criterion"),
            H("The specified code and the longest surviving ambiguity"),
            StatementSource.FromAuthor(Disp(Claim())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let A be an essential directed multigraph on a finite nonempty vertex set, and let the finite state set Q map onto its vertices. Each actual numbered edge a has a predecessor function from its whole terminal fiber to its initial fiber. The lifted graph has one edge with identity (a,q) from the predecessor of q to q. Count all these edges at each pair of endpoints to form C, and assume C is essential as well. Ranking and decoding at fixed endpoints preserve the full edge identity.")),
                Paragraph(Text("Use all legal bilateral edge histories indexed by the integers, with discrete edge alphabets and the product subspace topology. The code pi reads the original edge a at every position. It is continuous and commutes with the one-step shifts. A conjugacy here is a homeomorphism whose forward function is this pi and which commutes with these shifts.")),
                Paragraph(Text("A pair vertex is a two-element unordered subset of one state fiber. A numbered edge a gives an arrow from a terminal pair to the image pair under its predecessor function only when the image still has two elements. These arrows trace ambiguity backwards in real time. P counts these vertices exactly: sum over all base vertices of the binomial coefficient of the fiber cardinality and two.")),
                Paragraph(Text("For every natural depth d, failure of forgetting on a compatible d-edge path is equivalent to a d-edge walk in this pair graph. Forgetting quantifies over every actual numbered path and its entire terminal fiber. At depth zero it uses the identity in every fiber.")),
                Paragraph(Text("The four equivalent conditions are injectivity of pi, conjugacy of pi, existence of a finite forgetting depth, and absence of directed cycles in the pair graph. If P is zero, the least forgetting depth is zero. If P is positive and the pair graph is acyclic, its attained greatest walk length ell exists, the least forgetting depth is ell plus one, and every depth at most ell fails.")),
                Paragraph(Text("At any forgetting depth d, the inverse exists on every legal base history, is continuous, satisfies both inverse laws, and commutes with the shifts. Its output edge at position i depends only on the base edges at positions i through i+d, including the last edge. The case d equal to zero uses the singleton base fibers.")),
                Paragraph(Text("If no finite depth forgets, a simple pair cycle has a positive length c at most P. Reverse its actual edge labels to obtain a closed base word. The incoming composite either fixes the two starting states or exchanges them. Its square fixes both, so two copies of the word have two distinct closed lifted words of length 2c.")),
                Paragraph(Text("Repeating these actual closed lifted words in both integer directions produces different legal C histories with the same image under pi. The wraparound edges, including every negative index, satisfy the original endpoint equations. Their common image has period c, and both lifted histories have period 2c; smaller least periods are allowed.")),
                Paragraph(Text("Consequently pi is a conjugacy exactly when no two distinct histories with the same pi-image have a common positive lift period at most 2P. The equivalent test may instead bound each lift period separately by 2P. These tests concern only this specified original-edge code."))),
            DescribeRole.Theorem))));

    private static Formula Claim()
    {
        Formula l = F.Id("L"), p = F.Id("P"), pi = F.Id("pi");
        Formula d = F.Id("d"), ell = F.Id("ell"), c = F.Id("c");
        Formula forget = Call("Forgets", l, d);
        Formula finiteForget = Some(forget, B("d", F.Id("Nat")));
        Formula acyclic = Call("Acyclic", Call("PairGraph", l));
        Formula conjugacy = Call("SpecifiedConjugacy", pi);
        Formula equivalences = And(Iff(Call("Injective", pi), conjugacy),
            And(Iff(conjugacy, finiteForget), Iff(finiteForget, acyclic)));
        Formula exactMemory = And(
            Imp(Equal(p, D(0)), Call("IsLeastForgets", l, D(0))),
            Imp(And(Lt(D(0), p), acyclic), Some(
                And(Call("GreatestPairWalkLength", l, ell),
                    And(Call("IsLeastForgets", l,
                        new Formula.Binary(ell, FormulaBinaryOperator.Add, D(1))),
                        All(Imp(Le(d, ell), Call("NotForgets", l, d)), B("d", F.Id("Nat"))))),
                B("ell", F.Id("Nat")))));
        Formula collision = Imp(Call("NotFiniteForgetting", l), Some(
            And(Lt(D(0), c), And(Le(c, p), Some(
                And(Call("Distinct", F.Id("x"), F.Id("y")),
                    And(Equal(Call("Apply", pi, F.Id("x")), Call("Apply", pi, F.Id("y"))),
                        And(Call("Periodic", Call("Apply", pi, F.Id("x")), c),
                            And(Call("Periodic", F.Id("x"), Twice(c)),
                                Call("Periodic", F.Id("y"), Twice(c)))))),
                B("x", Call("Path", F.Id("C"))), B("y", Call("Path", F.Id("C")))))),
            B("c", F.Id("Nat"))));
        Formula body = And(Equal(Call("Card", Call("PairVertices", l)), p),
            And(All(Iff(Call("NotForgets", l, d), Call("PairWalk", l, d)), B("d", F.Id("Nat"))),
                And(equivalences, And(exactMemory,
                    And(All(Imp(forget, Call("ContinuousInverseWithEdgeWindow", pi, d)),
                        B("d", F.Id("Nat"))),
                        And(collision, And(Iff(conjugacy, Call("NoCommonPeriodCollision", pi, Twice(p))),
                            Iff(conjugacy, Call("NoIndividuallyBoundedPeriodCollision", pi, Twice(p))))))))));
        return All(Imp(And(Call("Essential", F.Id("A")), Call("Essential", F.Id("C"))), body),
            B("n", F.Id("PositiveNat")), B("Q", F.Id("FiniteType")),
            B("A", Call("CountMat", F.Id("n"), F.Id("n"))),
            B("L", Call("IncomingLift", F.Id("A"), F.Id("Q"))),
            B("C", Call("ActualCountedLift", l)), B("pi", Call("OriginalEdgeReadout", l)),
            B("P", Call("SumFiberChooseTwo", l)));
    }
}
