using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental.CycleGeodesic;

internal sealed class CycleGeodesicMidpointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/rivin2026permanents");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The midpoint formula holds with a uniform quadratic error and even-dimensional vanishing.", H("CycleGeodesicMidpoint"),
        Blocks(
            Node("midpointscale", "midpointScale", Disp(All("n", Naturals(), Equal(Call("midpointScale", F.Id("n")), Mul(Mul(Pow(Negate(D(1)), Apply(Qualified("Nat", "div"), Apply(Qualified("Nat", "sub"), F.Id("n"), D(1)), D(2))), D(2)), Cast(Apply(Qualified("Real", "exp"), Negate(Cast(F.Id("n"), Reals()))), Complexes()))))),
                Blocks(Paragraph(Text("The alternating leading scale uses natural subtraction and natural division in its exponent, namely Nat.div (Nat.sub n 1) 2. The real exponential is cast to the complex numbers."))), DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("midpoint-even-of-product", "midpoint_even_of_product", Disp(ImpliesTo(F.Id("ProductFormula"), All("n", Naturals(), ImpliesTo(LeqTo(D(1), F.Id("n")), ImpliesTo(Call("Even", F.Id("n")), Equal(Apply(Qualified("Matrix", "permanent"), Call("gamma", F.Id("n"), Frac(D(1), D(2)))), D(0))))))),
                Blocks(Paragraph(Text("For a positive even dimension, the middle factor in the product is zero."))), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("stirlingerror", "stirlingError", Disp(All("n", Naturals(), Equal(Call("stirlingError", F.Id("n")), Sub(Apply(Qualified("Real", "log"), Apply(Qualified("Stirling", "stirlingSeq"), F.Id("n"))), Apply(Qualified("Real", "log"), Apply(Qualified("Real", "sqrt"), Qualified("Real", "pi"))))))),
                Blocks(Paragraph(Text("This logarithmic error measures the Stirling sequence relative to its limiting value."))), DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("midpointamplitude", "midpointAmplitude", Disp(All("m", Naturals(), Equal(Call("midpointAmplitude", F.Id("m")), Frac(Pow(Cast(Apply(Qualified("Nat", "factorial"), Add(Mul(D(2), F.Id("m")), D(1))), Reals()), D(2)), Mul(Mul(Pow(D(2), Mul(D(2), F.Id("m"))), Pow(Cast(Apply(Qualified("Nat", "factorial"), F.Id("m")), Reals()), D(2))), Pow(Add(Mul(D(2), Cast(F.Id("m"), Reals())), D(1)), Add(Mul(D(2), F.Id("m")), D(2)))))))),
                Blocks(Paragraph(Text("The positive amplitude is the literal factorial expression for an odd dimension."))), DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("midpointratio", "midpointRatio", Disp(All("m", Naturals(), Equal(Call("midpointRatio", F.Id("m")), Frac(Call("midpointAmplitude", F.Id("m")), Mul(D(2), Apply(Qualified("Real", "exp"), Negate(Add(Mul(D(2), Cast(F.Id("m"), Reals())), D(1))))))))),
                Blocks(Paragraph(Text("The amplitude is normalized by its leading exponential scale."))), DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("midpointlogratio", "midpointLogRatio", Disp(All("m", Naturals(), Equal(Call("midpointLogRatio", F.Id("m")), Add(Sub(Mul(Add(Mul(D(2), Cast(F.Id("m"), Reals())), D(1)), Negate(Apply(Qualified("Real", "log"), Sub(D(1), Frac(D(1), Add(Mul(D(2), Cast(F.Id("m"), Reals())), D(1))))))), D(1)), Sub(Mul(D(2), Call("stirlingError", Add(Mul(D(2), F.Id("m")), D(1)))), Mul(D(2), Call("stirlingError", F.Id("m")))))))),
                Blocks(Paragraph(Text("The expression separates the logarithmic mesh correction from the two Stirling errors."))), DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("midpointamplitude-pos", "midpointAmplitude_pos", Disp(All("m", Naturals(), LtTo(D(0), Call("midpointAmplitude", F.Id("m"))))),
                Blocks(Paragraph(Text("Every factorial and denominator factor is positive."))), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("product-odd-amplitude", "product_odd_amplitude", Disp(All("m", Naturals(), Equal(Call("productValue", Add(Mul(D(2), F.Id("m")), D(1)), Negate(D(1))), Mul(Pow(Negate(D(1)), F.Id("m")), Cast(Call("midpointAmplitude", F.Id("m")), Complexes()))))),
                Blocks(Paragraph(Text("Splitting the odd factors into positive and negative factors gives the alternating amplitude."))), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("midpoint-ratio-of-product", "midpoint_ratio_of_product", Disp(ImpliesTo(F.Id("ProductFormula"), All("m", Naturals(), Equal(Frac(Apply(Qualified("Matrix", "permanent"), Call("gamma", Add(Mul(D(2), F.Id("m")), D(1)), Frac(D(1), D(2)))), Call("midpointScale", Add(Mul(D(2), F.Id("m")), D(1)))), Cast(Call("midpointRatio", F.Id("m")), Complexes()))))),
                Blocks(Paragraph(Text("The exact product identifies the permanent ratio with the positive real ratio."))), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("log-midpointratio", "log_midpointRatio", Disp(All("m", Naturals(), ImpliesTo(NeqTo(F.Id("m"), D(0)), Equal(Apply(Qualified("Real", "log"), Call("midpointRatio", F.Id("m"))), Call("midpointLogRatio", F.Id("m")))))),
                Blocks(Paragraph(Text("The logarithmic factorial identity applies for positive m."))), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("midpointlogratio-abs-le", "midpointLogRatio_abs_le", Disp(All("m", Naturals(), ImpliesTo(LeqTo(D(1), F.Id("m")), LeqTo(Abs(Call("midpointLogRatio", F.Id("m"))), Frac(D(2), Add(Mul(D(2), Cast(F.Id("m"), Reals())), D(1))))))),
                Blocks(Paragraph(Text("Telescoping the Stirling bounds gives a logarithmic error bounded by twice the reciprocal dimension."))), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("midpointratio-second-order", "midpointRatio_second_order", Disp(All("m", Naturals(), LeqTo(Abs(Sub(Sub(Call("midpointRatio", F.Id("m")), D(1)), Frac(D(1), Mul(D(3), Add(Mul(D(2), Cast(F.Id("m"), Reals())), D(1)))))), Frac(D(1, 6), Pow(Add(Mul(D(2), Cast(F.Id("m"), Reals())), D(1)), D(2)))))),
                Blocks(Paragraph(Text("The explicit remainder is uniform over every odd positive dimension, including n = 1."))), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("claim2", "claim2", Disp(IffTo(F.Id("claim2"), And(Parenthesized(ExistsOver("C", Reals(), And(Parenthesized(LeqTo(D(0), F.Id("C"))), Parenthesized(All("n", Naturals(), ImpliesTo(LeqTo(D(1), F.Id("n")), ImpliesTo(Call("Odd", F.Id("n")), LeqTo(Norm(Sub(Sub(Frac(Apply(Qualified("Matrix", "permanent"), Call("gamma", F.Id("n"), Frac(D(1), D(2)))), Call("midpointScale", F.Id("n"))), D(1)), Frac(D(1), Mul(D(3), Cast(F.Id("n"), Complexes()))))), Frac(F.Id("C"), Pow(Cast(F.Id("n"), Reals()), D(2))))))))))), Parenthesized(All("n", Naturals(), ImpliesTo(LeqTo(D(1), F.Id("n")), ImpliesTo(Call("Even", F.Id("n")), Equal(Apply(Qualified("Matrix", "permanent"), Call("gamma", F.Id("n"), Frac(D(1), D(2)))), D(0))))))))),
                Blocks(Paragraph(
                    Text("Page 19, Section 8.4, Open Problem 2: \"Prove the midpoint formula "),
                    Text("perm(γ(1/2)) = (-1)^((n-1)/2) · 2e^(-n)(1 + 1/(3n) + O(n^(-2)))"),
                    Text(".\" The norm bound encodes the big-O term uniformly over positive odd n. Observation 5 on page 8 supplies the even-dimensional zero clause."))), DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result2", "result2", Disp(And(Parenthesized(ExistsOver("C", Reals(), And(Parenthesized(LeqTo(D(0), F.Id("C"))), Parenthesized(All("n", Naturals(), ImpliesTo(LeqTo(D(1), F.Id("n")), ImpliesTo(Call("Odd", F.Id("n")), LeqTo(Norm(Sub(Sub(Frac(Apply(Qualified("Matrix", "permanent"), Call("gamma", F.Id("n"), Frac(D(1), D(2)))), Call("midpointScale", F.Id("n"))), D(1)), Frac(D(1), Mul(D(3), Cast(F.Id("n"), Complexes()))))), Frac(F.Id("C"), Pow(Cast(F.Id("n"), Reals()), D(2))))))))))), Parenthesized(All("n", Naturals(), ImpliesTo(LeqTo(D(1), F.Id("n")), ImpliesTo(Call("Even", F.Id("n")), Equal(Apply(Qualified("Matrix", "permanent"), Call("gamma", F.Id("n"), Frac(D(1), D(2)))), D(0)))))))),
                Blocks(Paragraph(Text("The permanent has the stated alternating exponential scale and the 1/(3n) correction. A single constant C = 16 works for all positive odd n; every positive even n gives zero."))), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("rivin-2026-cycle-geodesic-midpoint-formula"),
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
    private static Formula ExistsOver(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Colon, t));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Abs(Formula a) => new Formula.Absolute(a);
    private static Formula NeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ImpliesTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
}
