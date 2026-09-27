using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class FiniteSourceClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual recursive image is closed in the critical weighted norm, and the "
        + "norm closure of finite-source outputs has vanishing antidiagonal tails.",
        H("Finite Source Closure"),
        Blocks(Describe.Lean(
            DescribeId.Create("critical-recursive-image-closure"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/SeriesInequalities/FiniteSourceClosure."
                + "critical_recursive_image_closure"),
            H("Closure of the actual finite-source image"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let K be a real-like field, so that K can be the real or complex "
                    + "numbers. The extension has boundary E(a)(n,0)=a(n) and recurrence "
                    + "E(a)(n,k+1)=E(a)(n+1,k)-sum over j=0,...,k of E(a)(n,j)a(k-j). "
                    + "All source coordinates have norm at most A.")),
                Paragraph(Text(
                    "WeightedArray(K) is the space of bounded K-valued functions on pairs "
                    + "of natural numbers, with the supremum norm. An unweighted array T "
                    + "is represented by U(n,k)=rho^(n+k) times T(n,k). Because rho is "
                    + "positive, division by that weight recovers every entry of T. "
                    + "The norm of U is exactly the supremum of rho^(n+k) norm(T(n,k)). "
                    + "In the displayed formula, smul denotes real scalar multiplication.")),
                Paragraph(Text(
                    "The set actualImage(A,rho) consists of these weighted outputs of "
                    + "all admissible boundaries. The set finiteSourceImage(A,rho) uses "
                    + "boundaries that vanish beyond some natural index M. Their recursive "
                    + "outputs retain every column; finite input support does not mean "
                    + "finite output support.")),
                Paragraph(Text(
                    "For a weighted array U, tail(U,L) is the supremum of norm(U(n,k)) "
                    + "over n+k at least L. The set vanishingTails consists of the arrays "
                    + "for which these suprema tend to zero. All closures and closedness "
                    + "assertions use the supremum norm on WeightedArray(K).")),
                Paragraph(Text(
                    "At the critical relation A rho=(1-rho)^2, each finite convolution "
                    + "has mass rho+A sum over i=0,...,k of rho^(i+1) at most one. "
                    + "Strong column induction gives norm(E(a)(n,k)) rho^k at most A "
                    + "for every bounded boundary. Since rho^n is at most one, this "
                    + "constructs the weighted output with norm at most A.")),
                Paragraph(Text(
                    "Recover a source from a weighted array by a(n)=rho^(-n) U(n,0). "
                    + "Each recovered source coordinate is continuous in U. Strong "
                    + "induction through the subtraction, multiplication and finite sums "
                    + "in the recurrence proves continuity of each output coordinate in "
                    + "the product topology of the boundary. The actual image is thus "
                    + "exactly the simultaneous closed conditions that the recovered "
                    + "source obeys the amplitude bound and reproduces every coordinate. "
                    + "This proves image closedness without norm continuity of the full "
                    + "source-to-output map.")),
                Paragraph(Text(
                    "The tail suprema satisfy tail(U,L) at most norm(U-V)+tail(V,L). "
                    + "A norm approximation within epsilon/2 and a tail bound of "
                    + "epsilon/2 prove that vanishingTails is closed. Finite-source "
                    + "critical tail decay places every finite-source output in this "
                    + "closed set. Closedness of the actual image then gives the stated "
                    + "inclusion for the norm closure. No reverse inclusion or compactness "
                    + "of the actual image is asserted."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula field = F.Id("K");
        Formula a = F.Id("A");
        Formula rho = F.Id("rho");
        Formula boundary = F.Id("a");
        Formula u = F.Id("U");
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula space = Call("WeightedArray", field);
        Formula image = Call("actualImage", a, rho);
        Formula finiteImage = Call("finiteSourceImage", a, rho);
        Formula hypotheses = And(Call("RCLike", field),
            And(Lt(D(0), a), And(Lt(D(0), rho), And(Lt(rho, D(1)),
                EqFormula(Mul(a, rho), Pow(Sub(D(1), rho), D(2)))))));
        Formula bound = ForAll([Bound("n", naturals)],
            LeqFormula(Call("norm", Call("a", n)), a));
        Formula coordinates = ForAll([Bound("n", naturals), Bound("k", naturals)],
            EqFormula(Call("U", n, k),
                Call("smul", Pow(rho, Add(n, k)), Call("extension", boundary, n, k))));
        Formula representation = ForAll([Bound("a", Seq(naturals, To, Sp, field))],
            Implies(bound, new Formula.BindMany(FormulaQuantifier.Exists,
                [Bound("U", space)], And(LeqFormula(Call("norm", u), a), coordinates))));
        Formula inclusion = ForAll([Bound("U", space)],
            Implies(Member(u, Call("closure", finiteImage)),
                And(Member(u, image), Member(u, F.Id("vanishingTails")))));
        return Disp(ForAll([Bound("K", F.Id("Type")), Bound("A", reals), Bound("rho", reals)],
            Implies(hypotheses, And(representation, And(Call("IsClosed", image), inclusion)))));
    }

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula EqFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LeqFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
