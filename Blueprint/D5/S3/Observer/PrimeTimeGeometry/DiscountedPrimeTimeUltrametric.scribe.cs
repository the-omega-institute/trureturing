using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.PrimeTimeGeometry;

internal sealed class DiscountedPrimeTimeUltrametricDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/PrimeTimeGeometry/DiscountedPrimeTimeUltrametric.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The discounted finite-family prime-time distance obeys the strong triangle law.",
        H("Discounted Prime-Time Ultrametric"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discounted-prime-time-distance"),
                Handle("discountedPrimeTimeDistance"),
                H("Discounted prime-time distance"),
                StatementSource.FromAuthor(DistanceDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite observer budget J, take the real supremum over each selected "
                        + "index i and each nonnegative time n. The summand is the coordinate "
                        + "weight times gamma to the nth power times the zero-or-one "
                        + "discrepancy between the two readouts after n updates.")),
                    Paragraph(Text(
                        "Source-boundary open: the source does not define a real supremum for "
                            + "the empty coordinate family J = emptyset. The Lean iSup expression "
                            + "has a totalized empty-budget behavior supplied by its ambient order "
                            + "structure; that behavior is formalization-specific, not a source "
                            + "convention, and remains open pending an authoritative source clause."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discounted-prime-time-distance-strong-triangle"),
                Handle("discounted_prime_time_distance_strong_triangle"),
                H("Prime-time prediction distance obeys the strong triangle inequality"),
                StatementSource.FromAuthor(StrongTriangleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source standing carrier clause requires strictly positive weight "
                            + "on every coordinate i in I, while gamma belongs to (0,1]. Both are "
                            + "section-level clauses of the source volume, cited here so the claim "
                            + "can be checked against the source rather than taken on this "
                            + "document's word. Source line 2016, immediately before Definition "
                            + "33.1, specifies a positive weight w_i for every coordinate; the "
                            + "section 33 heading, standing before both Definition 33.1 and "
                            + "Theorem 33.1, sets 0 < gamma <= 1; and source line 2083 restates "
                            + "both together as the hypothesis that all weights are positive and "
                            + "gamma > 0. The source states these in LaTeX; they are transcribed "
                            + "to plain text here because Scribe text runs carry no raw LaTeX "
                            + "delimiters, and the verbatim quotations are kept in the Lean "
                            + "docstring instead. They are therefore not premises introduced "
                            + "here; the atom for Theorem 33.1 is a slice that does not carry "
                            + "them. The proof only invokes that positivity on the selected "
                            + "finite budget J, but the public theorem preserves the source's "
                            + "global premise.")),
                    Paragraph(Text(
                        "The source is silent on the empty-budget supremum (J = emptyset), so "
                            + "that case is an open source boundary rather than an added premise "
                            + "or an assigned source value.")),
                    Paragraph(Text(
                        "The finite budget, the bounded discount powers, and the zero-or-one "
                            + "coordinate discrepancy bound every supremum by the sum of the "
                            + "selected weights. The existing weighted joint strong triangle "
                            + "theorem supplies the pointwise law, and ciSup_sup_eq moves the "
                            + "maximum through the prime-time supremum."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric")),
        ]));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create(DeclarationPrefix + name);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Distance(Formula first, Formula second) =>
        Seq(
            F.Id("d"), Underscore,
            Grp(F.Id("J"), Comma, F.Id("gamma")), Caret, F.Id("F"),
            Open, first, Comma, Sp, second, Close);

    private static Formula DistanceDefinitionFormula()
    {
        Formula i = F.Id("i");
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula orbitX = Call("q", i, Call("iterate", F.Id("F"), n, x));
        Formula orbitY = Call("q", i, Call("iterate", F.Id("F"), n, y));
        Formula discrepancy = Call("discreteOutputDistance", orbitX, orbitY);
        Formula index = Seq(
            i, InMacro, Sp, F.Id("J"), Comma, Sp,
            n, InMacro, Sp, Mathbb, Grp(F.Id("N")));
        Formula supremum = Seq(
            Operatorname, Grp(F.Id("sup")), Underscore, Grp(index), Sp,
            Call("w", i), Sp, F.Id("gamma"), Caret, n, Sp, discrepancy);

        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, y, InMacro, Sp, F.Id("X"), Comma,
            RowBreak, Distance(x, y), Sp, Eq, Sp, supremum, Dot));
    }

    private static Formula StrongTriangleFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula index = F.Id("I");
        Formula state = F.Id("X");
        Formula outputs = F.Id("O");
        Formula selected = F.Id("J");
        Formula weight = F.Id("w");
        Formula readout = F.Id("q");
        Formula update = F.Id("F");
        Formula gamma = F.Id("gamma");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula outputFamily = Seq(index, Sp, To, Sp, type);
        Formula indexedReadout = Seq(
            Forall, Sp, F.Id("i"), Colon, Sp, index, Comma, Sp,
            state, Sp, To, Sp, Call("O", F.Id("i")));
        Formula positiveWeights = Seq(
            Forall, Sp, F.Id("i"), Colon, Sp, index, Comma, Sp,
            D(0), Sp, Lt, Sp, Call("w", F.Id("i")));
        Formula gammaRange = Seq(
            gamma, InMacro, Sp, Open, D(0), Comma, Sp, D(1), CloseBracket);
        Formula conclusion = Seq(
            Distance(x, z), Sp, Leq, Sp, Max, Open,
            Distance(x, y), Comma, Sp, Distance(y, z), Close);
        Formula theoremBody = Seq(
            Grp(positiveWeights), Sp, Rightarrow, RowBreak,
            gammaRange, Sp, Rightarrow, RowBreak,
            Forall, Sp, x, Comma, Sp, y, Comma, Sp, z,
            InMacro, Sp, state, Comma, RowBreak, conclusion);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("I"), type),
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), type),
                new Formula.BoundVariable(FormulaIdentifier.Create("O"), outputFamily),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("J"), Call("Finset", index)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("w"), Seq(index, Sp, To, Sp, reals)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("q"), indexedReadout),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("F"), Seq(state, Sp, To, Sp, state)),
                new Formula.BoundVariable(FormulaIdentifier.Create("gamma"), reals),
            ],
            theoremBody));
    }
}
