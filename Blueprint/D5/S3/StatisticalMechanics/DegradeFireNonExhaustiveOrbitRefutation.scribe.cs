using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class DegradeFireNonExhaustiveOrbitRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/fernandez2018revisiting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A saturated three-cell degrade-and-fire system has a nine-firing periodic trajectory with repeated firing labels.",
        H("A non-exhaustive periodic degrade-and-fire trajectory"),
        Blocks(
            Paragraph(Text(
                "Cell labels are 0-indexed in Lean: 0, 1 and 2 correspond respectively to the source's labels 1, 2 and 3. "
                    + "Vectors written with ![a,b,c] are functions on Fin 3 in that order. "
                    + "The threshold θ is the source's η. "
                    + "The source locators below refer to DynamicsDFNetworksRevised.tex in arXiv:1809.03228v1.")),
            Node("coupling", "coupling", "The unidirectional coupling matrix", CouplingFormula(),
                "The circulant with first column (1 − ε, ε, 0) has rows (1 − ε, 0, ε), "
                    + "(ε, 1 − ε, 0) and (0, ε, 1 − ε). This is the matrix of Section 4, "
                    + "lines 239–247. The definition allows every real ε; positivity and the threshold "
                    + "restrictions enter the claim.", AssessedProvenance.FromLiterature(Source)),
            Node("reset", "reset", "Resetting one coordinate", ResetFormula(),
                "Replace coordinate i of x by the real number 1 and leave every other coordinate unchanged. "
                    + "This is the instantaneous firing rule in lines 56–64.",
                AssessedProvenance.FromLiterature(Source)),
            Node("is-run", "IsRun", "Successive unique firings", RunFormula(),
                "The functions s, lab and τ give the post-firing configurations, the next firing cell "
                    + "and the elapsed time until that firing. At every natural k the elapsed time is positive. "
                    + "Every repressor is strictly above θ before that time; at the endpoint the selected "
                    + "cell is at or below θ and every other cell is strictly above it. Coordinates are "
                    + "pairwise distinct throughout the closed degrading segment and immediately after resetting. "
                    + "The final equality relates the next configuration to that reset. These conditions express "
                    + "the dynamics of lines 52–64 and the post-firing description and distinctness restriction "
                    + "of lines 249–255. No separate coordinate-range assumption is part of this predicate.",
                AssessedProvenance.FromLiterature(Source)),
            Node("is-periodic", "IsPeriodic", "Periodicity of post-firing configurations", PeriodicFormula(),
                "A positive natural number p is a period when s(k + p) = s(k) for every natural k. "
                    + "This is periodicity indexed by firings, as in the return condition of lines 377–390; "
                    + "the definition does not separately assert periodicity of lab or τ.",
                AssessedProvenance.FromLiterature(Source)),
            Node("is-exhaustive", "IsExhaustive", "Exhaustive firing sequences", ExhaustiveFormula(),
                "Every three consecutive labels must form a bijection from Fin 3 to Fin 3, so each cell "
                    + "occurs exactly once in every such window. This is the length-three permutation "
                    + "condition in line 68, with labels shifted from 1, 2, 3 to 0, 1, 2.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "claim", "The proposed exclusion of non-exhaustive periodic trajectories",
                Equal(Typed(Local("claim"), Qualified("Prop")), Parenthesized(ClaimProposition())),
                "For 0 < θ < 1 and 1/2 < ε < 1 − θ, the assertion says that every run whose initial "
                    + "repressors are strictly above θ and whose configurations are periodic has an exhaustive "
                    + "firing sequence. This is the statement in the Concluding Remarks, line 373, that the "
                    + "impossibility should extend to every other periodic trajectory with non-exhaustive "
                    + "firing in the right transition graph. The parameter range and graph are specified "
                    + "in lines 239–257. The run predicate makes uniqueness of each firing and distinctness "
                    + "along each segment explicit. The assertion concerns periodic trajectories, without "
                    + "an attraction or asymptotic rarity conclusion.", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("A nine-firing counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimProposition())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take θ = 3/20 and ε = 4/5. Define s by repeating the following nine configurations, "
                            + "indexed from zero: (11/32,0,1), (3/16,1,27/32), (0,1,19/32), "
                            + "(0,1,11/32), (1,27/32,3/16), (1,19/32,0), (1,11/32,0), "
                            + "(27/32,3/16,1), (19/32,0,1). Define lab by repeating "
                            + "(1,1,1,0,0,0,2,2,2), and τ by repeating (5/32,1/4,1/4) three times. "
                            + "Each function at k is the corresponding entry at k modulo 9.")),
                    Paragraph(Text(
                        "For a three-coordinate vector, the three pairwise inequalities imply injectivity. "
                            + "For each of the nine configurations, its assigned time is positive. "
                            + "For each coordinate j and each real t less than that time, substituting "
                            + "the circulant entries and the formula max(s(k)(j) − t, 0) gives a repressor "
                            + "strictly above 3/20. Splitting according to the sign of each truncated "
                            + "coordinate reduces these inequalities to linear inequalities in t. "
                            + "At the endpoint the selected cell has repressor 3/20, while the other two "
                            + "remain strictly above it. For the first three endpoints the repressor triples "
                            + "are (57/80,3/20,27/160), (19/40,3/20,23/32) and (11/40,3/20,107/160); "
                            + "substitution gives the endpoint inequalities for all nine configurations.")),
                    Paragraph(Text(
                        "The same sign splits show that the three degrading coordinates remain pairwise "
                            + "distinct for every t at most the assigned time, hence in particular on its "
                            + "closed nonnegative interval. Each succeeding configuration also has distinct "
                            + "coordinates. Coordinatewise substitution shows that resetting the selected "
                            + "endpoint coordinate to 1 gives exactly the next listed configuration, with "
                            + "the ninth followed by the first. These facts give all seven conditions in "
                            + "the run predicate for each of the nine positions.")),
                    Paragraph(Text(
                        "For arbitrary natural k, (k + 1) modulo 9 is the successor of k modulo 9 "
                            + "in Fin 9. Thus the nine segment computations give a run at every k. "
                            + "Initially the repressor triple is (139/160,11/40,1/5), with all three "
                            + "entries above 3/20. Adding 9 to k leaves its remainder unchanged, "
                            + "so s(k + 9) = s(k), and 9 is a positive period.")),
                    Paragraph(Text(
                        "The first three labels are all 1. If the label sequence were exhaustive, "
                            + "its first three-entry vector would be injective. Its values at the distinct "
                            + "indices 0 and 1 coincide, contradicting that injectivity. Finally, "
                            + "0 < 3/20 < 1 and 1/2 < 4/5 < 1 − 3/20. Applying the proposed universal "
                            + "assertion to these parameters and to s, lab and τ would therefore make "
                            + "this non-exhaustive sequence exhaustive, which is a contradiction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fernandez-2018-degrade-fire-non-exhaustive-orbit-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula CouplingFormula() => All("ε", Reals(),
        Equal(Typed(Call("coupling", X("ε")), At(Qualified("Matrix"), Cells(), Cells(), Reals())),
            At(Qualified("Matrix", "circulant"),
                Vector(Subtract(RealNumber(1), X("ε")), X("ε"), RealNumber(0)))));

    private static Formula ResetFormula() => All("x", Configuration(), All("i", Cells(),
        Equal(Typed(Call("reset", X("x"), X("i")), Configuration()),
            At(Qualified("Function", "update"), X("x"), X("i"), RealNumber(1)))));

    private static Formula RunFormula()
    {
        Formula time = At(X("τ"), X("k"));
        Formula next = At(X("s"), Add(X("k"), NatNumber(1)));
        Formula label = At(X("lab"), X("k"));
        Formula before = All("t", Reals(), Imp(LE(RealNumber(0), X("t")), Imp(Less(X("t"), time),
            All("j", Cells(), Less(X("θ"), Repressor(X("t"), X("j")))))));
        Formula endpoint = LE(Repressor(time, label), X("θ"));
        Formula others = All("j", Cells(), Imp(NotEqual(X("j"), label),
            Less(X("θ"), Repressor(time, X("j")))));
        Formula distinct = All("t", Reals(), Imp(LE(RealNumber(0), X("t")), Imp(LE(X("t"), time),
            At(Qualified("Function", "Injective"), Segment(X("t"))))));
        Formula body = All("k", Naturals(), And(Less(RealNumber(0), time), And(before, And(endpoint,
            And(others, And(distinct, And(At(Qualified("Function", "Injective"), next),
                Equal(next, Call("reset", Segment(time), label)))))))));
        return All("ε", Reals(), All("θ", Reals(), All("s", Configurations(),
            All("lab", Labels(), All("τ", Durations(),
                Equal(Typed(Call("IsRun", X("ε"), X("θ"), X("s"), X("lab"), X("τ")), Qualified("Prop")),
                    Parenthesized(body)))))));
    }

    private static Formula PeriodicFormula() => All("s", Configurations(),
        Equal(Typed(Call("IsPeriodic", X("s")), Qualified("Prop")),
            Some("p", Naturals(), And(Less(NatNumber(0), X("p")), All("k", Naturals(),
                Equal(At(X("s"), Add(X("k"), X("p"))), At(X("s"), X("k"))))))));

    private static Formula ExhaustiveFormula() => All("lab", Labels(),
        Equal(Typed(Call("IsExhaustive", X("lab")), Qualified("Prop")), All("k", Naturals(),
            At(Qualified("Function", "Bijective"), Vector(At(X("lab"), X("k")),
                At(X("lab"), Add(X("k"), NatNumber(1))),
                At(X("lab"), Add(X("k"), NatNumber(2))))))));

    private static Formula ClaimProposition()
    {
        Formula initial = All("j", Cells(), Less(X("θ"), At(
            At(Qualified("Matrix", "mulVec"), Call("coupling", X("ε")), At(X("s"), NatNumber(0))), X("j"))));
        Formula conclusion = All("s", Configurations(), All("lab", Labels(), All("τ", Durations(),
            Imp(initial, Imp(Call("IsRun", X("ε"), X("θ"), X("s"), X("lab"), X("τ")),
                Imp(Call("IsPeriodic", X("s")), Call("IsExhaustive", X("lab"))))))));
        return All("θ", Reals(), All("ε", Reals(), Imp(Less(RealNumber(0), X("θ")),
            Imp(Less(X("θ"), RealNumber(1)), Imp(Less(new Formula.Fraction(RealNumber(1), RealNumber(2)), X("ε")),
                Imp(Less(X("ε"), Subtract(RealNumber(1), X("θ"))), conclusion))))));
    }

    private static Formula Segment(Formula t) => At(
        Qualified("D5", "S3", "Geometry", "FiniteCoordinateTruncation", "cut"),
        t, At(X("s"), X("k")));
    private static Formula Repressor(Formula t, Formula j) => At(
        At(Qualified("Matrix", "mulVec"), Call("coupling", X("ε")), Segment(t)), j);
    private static Formula Cells() => At(Qualified("Fin"), NatNumber(3));
    private static Formula Configuration() => Arrow(Cells(), Reals());
    private static Formula Configurations() => Arrow(Naturals(), Configuration());
    private static Formula Labels() => Arrow(Naturals(), Cells());
    private static Formula Durations() => Arrow(Naturals(), Reals());
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula NatNumber(byte value) => Typed(D(value), Naturals());
    private static Formula RealNumber(byte value) => Typed(D(value), Reals());
    private static Formula Vector(Formula a, Formula b, Formula c) =>
        Seq(Bang, OpenBracket, a, Comma, Sp, b, Comma, Sp, c, CloseBracket);
    private static Formula Local(string name) => Qualified(
        "D5", "S3", "StatisticalMechanics", "DegradeFireNonExhaustiveOrbitRefutation", name);
    private static Formula Call(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula X(string name) => name switch
    {
        "ε" => Varepsilon,
        "θ" => Theta,
        "τ" => Tau,
        _ => F.Id(name),
    };
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula premise, Formula conclusion) => Arrow(premise, conclusion);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
