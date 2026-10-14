using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class NonlocalNonstabilizernessHaarMeanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/qian2025nonlocalnonstabilizerness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Appendix C density has integrable first moment 10/3 minus pi.",
        H("The Haar mean of non-local nonstabilizerness"),
        Blocks(
            Node("zc", "The square root in the density", "zC", ZFormula(),
                "Appendix C introduces z = √(4 − 3e^y) in (C5). This real-valued function is defined for every real y using the real square root.",
                AssessedProvenance.FromLiterature(Source)),
            Node("density", "The Appendix C density", "nnDensity", DensityFormula(),
                "Equation (C5) gives the density of y = M(x) for a Haar-random two-qubit pure state. The formula is used on 0 < y < ln(4/3), and the function is zero everywhere else, including both endpoints. Every exponential and square root is real.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Integrability and the exact first moment", "claim", ClaimFormula(),
                "The source asks in §III and Appendix C for a closed form of the mean ȳ ≡ ∫ yP(y)dy, with P given by (C5). The statement combines integrability of the first-moment function on the real line with the value 10/3 − π of its Lebesgue integral, taken with respect to volume. Through the substitution t = 1 − 2x, this mean equals ∫₀¹ M(x)·3(1 − 2x)² dx, the Haar average under (C1) and the source's Schmidt-weight density P(x) = 3(1 − 2x)². This equivalence is mathematical background and is not part of the formal statement.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("nn-haar-mean-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The first moment is 10/3 minus pi"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Put a = ln(4/3). The primitive F(t) = −t³ ln(t⁴ − t² + 1) + (4/3)t³ + 2t − 2(arctan(2t + √3) + arctan(2t − √3)) has derivative −3t² ln(t⁴ − t² + 1), with F(0) = 0 and F(1) = 10/3 − π. The last endpoint value follows from (2 + √3)(2 − √3) = 1 and the reciprocal identity for the real arctangent.")),
                    Paragraph(Text(
                        "For 0 < y < a, set w = √(4e^(−y) − 3) and t₋ = √((1 − w)/2), t₊ = √((1 + w)/2). Both branches satisfy t⁴ − t² + 1 = e^(−y), and (C5) becomes 3e^(−y)(t₋ + t₊)/(2w). Thus G(y) = F(t₋(y)) − F(t₊(y)) has derivative yP(y). Its endpoint values are G(0) = −(10/3 − π) and G(a) = 0.")),
                    Paragraph(Text(
                        "On this interval, 0 ≤ yP(y) ≤ a√3/√(a − y). The majorant is integrable because its endpoint singularity has exponent −1/2. The fundamental theorem of calculus gives the first moment as G(a) − G(0) = 10/3 − π. The integrand vanishes outside the interval, so integrability and the same integral value hold on the whole real line."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("qian-wang-2025-nonlocal-nonstabilizerness-haar-mean"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("nn-haar-mean-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Magic", "NonlocalNonstabilizernessHaarMean", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula RealCall(string name, Formula value) => At(Qualified("Real", name), value);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Divide(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) => Parenthesized(Seq(
        F.Text, Grp(X("if")), Sp, Parenthesized(condition), Sp, F.Text, Grp(X("then")), Sp, yes,
        Sp, F.Text, Grp(X("else")), Sp, no));

    private static Formula ZFormula() => All("y", Reals(), Equal(LocalCall("zC", X("y")),
        RealCall("sqrt", Subtract(D(4), Multiply(D(3), RealCall("exp", X("y")))))));

    private static Formula DensityFormula()
    {
        Formula y = X("y");
        Formula z = LocalCall("zC", y);
        Formula positiveHalfExp = RealCall("exp", Divide(y, D(2)));
        Formula negativeHalfExp = RealCall("exp", Divide(new Formula.Negate(y), D(2)));
        Formula prefactor = Divide(Multiply(D(3), negativeHalfExp),
            Multiply(Multiply(D(4), z), RealCall("sqrt",
                Multiply(D(2), Parenthesized(Subtract(RealCall("exp", y), D(1)))))));
        Formula first = Multiply(Parenthesized(Add(positiveHalfExp, z)),
            RealCall("sqrt", Subtract(D(1), Multiply(negativeHalfExp, z))));
        Formula second = Multiply(Parenthesized(Subtract(positiveHalfExp, z)),
            RealCall("sqrt", Add(D(1), Multiply(negativeHalfExp, z))));
        Formula support = And(Less(D(0), y), Less(y, RealCall("log", Divide(D(4), D(3)))));
        return All("y", Reals(), Equal(LocalCall("nnDensity", y),
            IfThenElse(support, Multiply(prefactor, Parenthesized(Add(first, second))), D(0))));
    }

    private static Formula Integrand() => Multiply(X("y"), LocalCall("nnDensity", X("y")));

    private static Formula ClaimFormula()
    {
        Formula function = Parenthesized(Seq(F.Text, Grp(X("fun")), Sp,
            Parenthesized(Seq(X("y"), Colon, Sp, Reals())), Sp, Mapsto, Sp, Integrand()));
        Formula integrability = At(Qualified("MeasureTheory", "Integrable"), function);
        Formula integral = Seq(Int, Sp, X("y"), Colon, Sp, Reals(), Comma, Sp, Parenthesized(Integrand()));
        Formula value = Subtract(Divide(D(1, 0), D(3)), Qualified("Real", "pi"));
        return Equivalent(Local("claim"), And(integrability, Equal(integral, value)));
    }
}
