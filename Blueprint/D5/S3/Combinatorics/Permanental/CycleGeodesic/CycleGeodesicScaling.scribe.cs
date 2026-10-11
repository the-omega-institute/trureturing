using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental.CycleGeodesic;

internal sealed class CycleGeodesicScalingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/rivin2026permanents");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The permanent rate tends to the closed cotangent expression, with the odd midpoint limit one.", H("CycleGeodesicScaling"),
        Blocks(
            Node("delta", "delta", Disp(All("t", Reals(), Equal(Call("delta", F.Id("t")), Call("min", F.Id("t"), Sub(D(1), F.Id("t")))))),
                Blocks(Paragraph(Text("Reflection selects the distance to the nearer endpoint."))), DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("rate", "rate", Disp(All("n", Naturals(), All("t", Reals(), Equal(Call("rate", F.Id("n"), F.Id("t")), Mul(Negate(Frac(D(1), Cast(F.Id("n"), Reals()))), Apply(Qualified("Real", "log"), Norm(Apply(Qualified("Matrix", "permanent"), Call("gamma", F.Id("n"), F.Id("t")))))))))),
                Blocks(Paragraph(
                    Text("Page 7, Observation 4: \"Define "),
                    Text("f(t) = -(1/n) ln|perm(γ(t)).|"),
                    Text(". Then f(t) converges to a universal function of t as n → ∞, with the properties:\" Here rate n t is the finite-dimensional quantity; the printed period inside the absolute value is a typographical artifact."))), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("universal", "universal", Disp(All("t", Reals(), Equal(Call("universal", F.Id("t")), Sub(D(1), Mul(Mul(Qualified("Real", "pi"), Call("delta", F.Id("t"))), Apply(Qualified("Real", "cot"), Mul(Qualified("Real", "pi"), Call("delta", F.Id("t"))))))))),
                Blocks(Paragraph(Text("This expression gives the closed form on the interior. Reflection symmetry, the continuous zero endpoint values and the quadratic Gaussian onset follow from the cotangent expression; the midpoint value is one. These analytic consequences explain the relation to Observation 4, while the settling theorem states the interior limit and the odd-dimensional midpoint limit."))), DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim3", "claim3", Disp(IffTo(F.Id("claim3"), And(Parenthesized(All("t", Reals(), ImpliesTo(LtTo(D(0), F.Id("t")), ImpliesTo(LtTo(F.Id("t"), D(1)), ImpliesTo(NeqTo(F.Id("t"), Frac(D(1), D(2))), Call("Tendsto", LambdaOf("n", Naturals(), Call("rate", F.Id("n"), F.Id("t"))), Qualified("Filter", "atTop"), Call("nhds", Call("universal", F.Id("t"))))))))), Parenthesized(Call("Tendsto", LambdaOf("m", Naturals(), Call("rate", Add(Mul(D(2), F.Id("m")), D(1)), Frac(D(1), D(2)))), Qualified("Filter", "atTop"), Call("nhds", D(1))))))),
                Blocks(Paragraph(Text("Page 19, Section 8.4, Open Problem 3: \"Find a closed form for the universal function f(t).\" The encoding identifies this function by the all-dimension rate limit at every t in (0,1) except 1/2, and by the odd-dimensional limit at 1/2. The endpoint values refer to continuous extension."))), DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result3", "result3", Disp(And(Parenthesized(All("t", Reals(), ImpliesTo(LtTo(D(0), F.Id("t")), ImpliesTo(LtTo(F.Id("t"), D(1)), ImpliesTo(NeqTo(F.Id("t"), Frac(D(1), D(2))), Call("Tendsto", LambdaOf("n", Naturals(), Call("rate", F.Id("n"), F.Id("t"))), Qualified("Filter", "atTop"), Call("nhds", Call("universal", F.Id("t"))))))))), Parenthesized(Call("Tendsto", LambdaOf("m", Naturals(), Call("rate", Add(Mul(D(2), F.Id("m")), D(1)), Frac(D(1), D(2)))), Qualified("Filter", "atTop"), Call("nhds", D(1)))))),
                Blocks(Paragraph(Text("The exact product turns the logarithmic rate into a left Riemann sum. Uniform continuity gives convergence away from the midpoint, and an elementary quadratic-logarithm integral gives 1 - pi delta cot(pi delta). The explicit odd midpoint estimate supplies the remaining limit."))), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("rivin-2026-cycle-geodesic-universal-function"),
                    ResolutionKind.Proved))), []));

    private static DocumentBlock Node(string id, string declaration, Formula formula,
        BlockSequence prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.FromAuthor(formula), provenance,
            prose, role, resolution);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Apply(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula LambdaOf(string n, Formula t, Formula b) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(n), Colon, t)), Sp, Mapsto, Sp, b);
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Colon, t));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ImpliesTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
}
