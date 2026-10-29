using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class SkewCoherencePolygamyMixedRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Resource/yu2017skewcoherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A mixed state on two by three levels violates skew-coherence polygamy.",
        H("A mixed-state refutation of skew-coherence polygamy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("skew-coherence"),
                DeclarationHandle.Create(Prefix + "skewCoherence"),
                H("Skew-information coherence in a reference basis"),
                StatementSource.FromAuthor(Disp(SkewCoherenceFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a finite reference index type and a complex matrix ρ, skewCoherence is "
                        + "one minus the sum over basis indices of the squared real diagonal entries "
                        + "of the positive continuous-functional-calculus square root of ρ. "
                        + "This is the diagonal reference-basis expression for the skew-information "
                        + "coherence in Yu's Lemma 1 (coherenceLy.tex, lines 170–178)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Mixed-state polygamy from total dimension six"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every pair of natural subsystem dimensions whose product is at least six, "
                        + "and every complex density matrix on their product index, the complement "
                        + "of skewCoherence of the joint state is at most the product of the two "
                        + "marginal complements. This is the repository's formal reading of the "
                        + "mixed-state conjecture stated in the source's discussion (coherenceLy.tex, "
                        + "lines 994–999) and Appendix D (lines 1370–1397)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A two by three counterexample"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Define the two-by-three witness matrix on Fin 2 × Fin 3 by the displayed rational entries: the Fin 3 "
                            + "coordinate 2 carries a two by two block with diagonal 1/4 and "
                            + "off-diagonal 3/17, while the other four coordinates have diagonal 1/8, "
                            + "entries 3/34 when exactly one local coordinate agrees, and 9/136 "
                            + "otherwise. Its two partial traces are the displayed two-by-two and "
                            + "three-by-three matrices.")),
                    Paragraph(Text(
                        "The explicit radical matrix for the joint witness is positive semidefinite because it is a positive "
                            + "real scaling of a weighted sum of six vector outer products. Its square "
                            + "is the witness matrix, and the witness is a density matrix by the conjugate-transpose square "
                            + "identity and a direct trace computation. Direct finite sums give its two stated partial traces.")),
                    Paragraph(Text(
                        "The explicit radical matrices for the two partial traces are positive semidefinite sums of "
                            + "vector outer products, and their squares are the corresponding partial traces. "
                            + "Uniqueness of the positive continuous-functional-calculus square root therefore "
                            + "identifies all three positive square roots used below.")),
                    Paragraph(Text(
                        "Reading the diagonal entries of these three roots yields, in order, "
                            + "the joint complement (25/34 + (1/2 + sqrt(145)/34))/2, "
                            + "the two-by-two marginal complement 1/2 + sqrt(145)/34, and "
                            + "the three-by-three marginal complement ((1/2 + sqrt(145)/34) + 1)/2.")),
                    Paragraph(Text(
                        "Subtracting the product of the two marginal values from the joint value gives "
                            + "(208 − 17 sqrt(145))/1156, which is positive because "
                            + "17 sqrt(145) < 208. If the claim held, instantiate it at m = 2, n = 3 "
                            + "and the witness matrix. Replacing its two partial traces by the displayed marginals would make "
                            + "the strict violation nonpositive, a contradiction. Thus result proves "
                            + "the negation of claim."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("yu-2017-skew-coherence-mixed-state-polygamy"),
                    ResolutionKind.Refuted))
        )));

    private static Formula X(string name) => F.Id(name);

    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0)
                items.Add(Dot);
            items.Add(X(part));
        }

        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Qualified(name), [.. arguments]);

    private static Formula QCall(params string[] parts) => Qualified(parts);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type,
            Parenthesized(body));

    private static Formula Nats() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrix(Formula rows, Formula columns) =>
        Call("Matrix", rows, columns, Complexes());
    private static Formula Product(Formula left, Formula right) =>
        Call("Prod", left, right);
    private static Formula PairIndex(Formula m, Formula n) =>
        Product(Fin(m), Fin(n));

    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Colon, Sp, type)), Sp,
            Parenthesized(body));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply,
            Parenthesized(right));

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract,
            Parenthesized(right));

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));

    private static Formula SkewCoherenceFormula()
    {
        Formula iota = X("iota"), rho = X("rho"), k = X("k");
        Formula index = iota;
        Formula squareRootEntry = Apply(Apply(QCall("CFC", "sqrt"), rho), k, k);
        Formula diagonalSquare = Power(
            Apply(QCall("Complex", "re"), squareRootEntry), Typed(D(2), Nats()));
        Formula body = Equal(
            Typed(Call("skewCoherence", rho), Reals()),
            Subtract(Typed(D(1), Reals()), SumOver(k, index, diagonalSquare)));
        return All("iota", X("Type"),
            Seq(OpenBracket, Call("Fintype", iota), CloseBracket, Sp,
                Seq(OpenBracket, Call("DecidableEq", iota), CloseBracket, Sp,
                    All("rho", Matrix(iota, iota), body))));
    }

    private static Formula ClaimBody()
    {
        Formula m = X("m"), n = X("n"), rho = X("rho");
        Formula index = PairIndex(m, n);
        Formula joint = Subtract(Typed(D(1), Reals()), Call("skewCoherence", rho));
        Formula right = Qualified(
            "D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation",
            "partialTraceRight");
        Formula left = Qualified(
            "D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation",
            "partialTraceLeft");
        Formula rightFactor = Subtract(
            Typed(D(1), Reals()), Call("skewCoherence", Apply(right, rho)));
        Formula leftFactor = Subtract(
            Typed(D(1), Reals()), Call("skewCoherence", Apply(left, rho)));
        Formula inequality = LessThanOrEqual(joint, Multiply(rightFactor, leftFactor));
        Formula density = Qualified(
            "D5", "S3", "Quantum", "Information", "SLDSpectralEnergy", "IsDensity");
        Formula quantified = All("m", Nats(), All("n", Nats(),
            Implies(
                LessThanOrEqual(Typed(D(6), Nats()), Multiply(m, n)),
                All("rho", Matrix(index, index),
                    Implies(Apply(density, rho), inequality)))));
        return Equal(Call("claim"), quantified);
    }

    private static Formula ClaimFormula() => ClaimBody();

    private static Formula ResultFormula() =>
        new Formula.Not(Parenthesized(Call("claim")));
}
