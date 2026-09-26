using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class L2KernelIntegralOperatorDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/L2KernelIntegralOperator.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/bredikhin2020hilbertschmidt");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every square-integrable complex kernel on a product of sigma-finite measure spaces defines a bounded integral operator, contractively and linearly in the kernel.",
        H("Integral Operators from Square-Integrable Kernels"),
        Blocks(Describe.Lean(
            DescribeId.Create("l2-kernel-integral-operator"),
            DeclarationHandle.Create(Module + "result"),
            H("The actual operator and its almost-everywhere integral formula"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("Let X and Y be arbitrary measurable spaces, with sigma-finite measures mu and nu. L2 denotes complex-valued square-integrable functions modulo almost-everywhere equality. CLM(C,E,F) denotes continuous complex linear maps from E to F, equipped with the operator norm.")),
                Paragraph(Text("There exists a continuous complex linear map A from L2(mu product nu) to CLM(C,L2(nu),L2(mu)), with norm at most one. For every kernel k and every input f, almost every x has an integrable section y mapped to k(x,y)f(y). The actual representative of A(k)(f) equals the Bochner integral of that section almost everywhere. The output norm is at most the kernel norm times the input norm.")),
                Paragraph(Text("The product is complex bilinear: neither k nor f is conjugated. A acts on equivalence classes, and replacing either function by an almost-everywhere equal representative preserves both the section integrability assertion and the output formula almost everywhere. Zero measures, infinite total measure and infinitely supported kernels and inputs are included.")),
                Paragraph(Text("Square integrability of k makes its squared norm integrable on the product. Fubini gives square-integrable sections almost everywhere and an integrable function of their squared norms. Cauchy--Schwarz on each section bounds the squared integral output by this function times the squared norm of f. The section integral is almost-everywhere strongly measurable; the bound proves its square integrability without assuming it.")),
                Paragraph(Text("Taking the resulting L2 equivalence class constructs the output. Almost-everywhere identities for addition and complex scalar multiplication, together with section integrability, give linearity in both arguments. The norm estimate makes this bilinear operation continuous and bounds the norm of the curried map by one. The construction is the classical square-integrable-kernel mechanism described by Bredikhin.")),
                Paragraph(Text("This theorem supplies an integral operator and the bound by the L2 norm of its kernel. It does not prove compactness, a spectral representation, or the sharper cosine-integral multiplier bound involving the inverse cutoff scale."))),
            DescribeRole.Theorem))));

    private static Formula C => F.Seq(F.Mathbb, F.Grp(F.Id("C")));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Lambda(string name, Formula domain, Formula body) =>
        F.Seq(F.Open, F.Id(name), F.Colon, domain, F.Mapsto, F.Sp, body, F.Close);
    private static Formula At(Formula f, params Formula[] args) =>
        F.Seq(f, F.Open, F.Seq(args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { F.Comma, x }).ToArray()), F.Close);
    private static Formula Norm(Formula x) => Call("norm", x);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);

    private static Formula TheoremFormula()
    {
        Formula xSpace = F.Id("X"), ySpace = F.Id("Y"), mx = F.Id("mx"), my = F.Id("my"),
            mu = F.Id("mu"), nu = F.Id("nu"), a = F.Id("A"), k = F.Id("k"), f = F.Id("f"),
            x = F.Id("x"), y = F.Id("y");
        Formula l2x = Call("Lp", C, F.D(2), mu), l2y = Call("Lp", C, F.D(2), nu),
            l2xy = Call("Lp", C, F.D(2), Call("prod", mu, nu));
        Formula product = Multiply(At(k, F.Seq(F.Open, x, F.Comma, y, F.Close)), At(f, y));
        Formula integral = F.Seq(F.Int, F.Underscore, F.Grp(nu), F.Sp, product, F.Sp, F.Id("d"), y);
        Formula output = At(At(a, k), f);
        Formula sections = Call("AE", mu, Lambda("x", xSpace,
            Call("Integrable", Lambda("y", ySpace, product), nu)));
        Formula values = Call("AE", mu, Lambda("x", xSpace, Equal(At(output, x), integral)));
        Formula conclusion = new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create("A"),
                Call("CLM", C, l2xy, Call("CLM", C, l2y, l2x)))],
            And(Le(Norm(a), F.D(1)), All("k", l2xy, All("f", l2y,
                And(sections, And(values, Le(Norm(output), Multiply(Norm(k), Norm(f)))))))));
        return F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("X"), F.Id("Type")),
             new Formula.BoundVariable(FormulaIdentifier.Create("Y"), F.Id("Type")),
             new Formula.BoundVariable(FormulaIdentifier.Create("mx"), Call("MeasurableSpace", xSpace)),
             new Formula.BoundVariable(FormulaIdentifier.Create("my"), Call("MeasurableSpace", ySpace)),
             new Formula.BoundVariable(FormulaIdentifier.Create("mu"), Call("Measure", xSpace, mx)),
             new Formula.BoundVariable(FormulaIdentifier.Create("nu"), Call("Measure", ySpace, my))],
            new Formula.Logic(And(Call("SigmaFinite", mu), Call("SigmaFinite", nu)),
                FormulaLogicOperator.Implies, conclusion)));
    }
}
