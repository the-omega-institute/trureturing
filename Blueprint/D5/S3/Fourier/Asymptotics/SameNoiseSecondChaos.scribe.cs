using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class SameNoiseSecondChaosDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite symmetric kernel sums have a well-defined centered-square integral on the same Gaussian noise.",
        H("Finite same-noise second integral"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("same-noise-finite-gram"),
                DeclarationHandle.Create(Module + "finiteGram"),
                H("Exact finite Gram identity"),
                StatementSource.FromAuthor(GramFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(
                    Paragraph(Text("Let mu be any finite measure, P a probability law, and W a fixed real linear isometry from H=L2(mu) to L2(P). Assume every W(f) has Gaussian law N(0,||f||^2). Spatial measure is not normalized. The rank-one class r(f,g) is represented by f(x)g(y) in L2(mu times mu); the symmetric subspace is the kernel of flip minus identity.")),
                    Paragraph(Text("For finite real coefficients c on H, let e(c) be the sum of c(h)r(h,h) and j(c) the sum of c(h)(W(h)^2-||h||^2). Exact scalar fourth moments and the sum-and-difference polarization give the centered-square covariance 2 inner(f,g)^2. Fubini gives the spatial rank-one inner products. Consequently inner(j(c),j(b))=2 inner(e(c),e(b)).")),
                    Paragraph(Text("The identity implies ||j(c)||=sqrt(2)||e(c)|| and e(c)=0 implies j(c)=0. Quotienting by the kernel of e therefore defines a bounded real linear map on the actual finite-kernel range. This map uses the given W and P throughout."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-noise-finite-frequency"),
                DeclarationHandle.Create(Module + "finiteFrequency_sameNoise"),
                H("Actual trigonometric frequency"),
                StatementSource.FromAuthor(FrequencyFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(
                    Paragraph(Text("For every real v, set c_v(x)=cos((pi/2)vx), s_v(x)=sin((pi/2)vx) and let 1 be the constant spatial vector. The finite coefficient vector consists of c_v and s_v with coefficient one and 1 with coefficient minus one. Its symmetric kernel has the actual representative cos((pi/2)v(x-y))-1.")),
                    Paragraph(Text("The norm-square sum ||c_v||^2+||s_v||^2=||1||^2 equals the original spatial mass. Centering therefore cancels exactly. The finite second integral has the almost-everywhere representative W(c_v)^2+W(s_v)^2-W(1)^2, which is |F(v)|^2-Y^2 for F(v)=W(c_v)-iW(s_v) and Y=W(1).")),
                    Paragraph(Text("The statements concern the actual finite-kernel range. Extension to all symmetric product-space kernels requires density of this range. Frequency integration and the singular logarithmic kernel require additional analytic statements."))),
                DescribeRole.Theorem))));

    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula At(string name, params Formula[] xs) => Call(name, xs);
    private static Formula Pow(Formula x, byte n) => new Formula.Power(x, F.D(n));
    private static Formula All(string name, Formula domain, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);

    private static Formula Hypotheses(Formula body, bool frequency)
    {
        Formula mu = F.Id("mu"), p = F.Id("P"), w = F.Id("W"), h = Call("Lp", F.Id("Real"), F.D(2), mu);
        Formula laws = All("f", h, At("HasLaw", At("evaluation", w, F.Id("f")),
            At("gaussianReal", F.D(0), At("toNNReal", Pow(At("norm", F.Id("f")), 2))), p));
        Formula conditions = new Formula.Logic(At("IsFiniteMeasure", mu), FormulaLogicOperator.And,
            new Formula.Logic(At("IsProbabilityMeasure", p), FormulaLogicOperator.And, laws));
        return F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("X"), frequency ? F.Id("Real") : F.Id("Type")),
             new Formula.BoundVariable(FormulaIdentifier.Create("SigmaX"), At("MeasurableSpace", F.Id("X"))),
             new Formula.BoundVariable(FormulaIdentifier.Create("mu"), At("Measure", F.Id("X"))),
             new Formula.BoundVariable(FormulaIdentifier.Create("Omega"), F.Id("Type")),
             new Formula.BoundVariable(FormulaIdentifier.Create("SigmaOmega"), At("MeasurableSpace", F.Id("Omega"))),
             new Formula.BoundVariable(FormulaIdentifier.Create("P"), At("Measure", F.Id("Omega"))),
             new Formula.BoundVariable(FormulaIdentifier.Create("W"), At("LinearIsometry", F.Id("Real"), h,
                At("Lp", F.Id("Real"), F.D(2), p)))],
            new Formula.Logic(conditions, FormulaLogicOperator.Implies, body)));
    }

    private static Formula GramFormula()
    {
        Formula mu = F.Id("mu"), p = F.Id("P"), w = F.Id("W"), law = F.Id("hW"),
            c = F.Id("c"), b = F.Id("b"), h = Call("Lp", F.Id("Real"), F.D(2), mu);
        Formula lhs = At("inner", At("finiteNoiseMap", mu, p, w, law, c), At("finiteNoiseMap", mu, p, w, law, b));
        Formula rhs = Multiply(F.D(2), At("inner", At("finiteKernelMap", mu, c), At("finiteKernelMap", mu, b)));
        return Hypotheses(All("c", At("Finsupp", h, F.Id("Real")),
            All("b", At("Finsupp", h, F.Id("Real")), Eq(lhs, rhs))), false);
    }

    private static Formula FrequencyFormula()
    {
        Formula mu = F.Id("mu"), p = F.Id("P"), w = F.Id("W"), v = F.Id("v"), omega = F.Id("omega");
        Formula value(string vector) => At("evaluation", w, At(vector, mu, v), omega);
        Formula rhs = F.Seq(Pow(value("cosineVector"), 2), F.Plus, Pow(value("sineVector"), 2),
            F.Minus, Pow(At("evaluation", w, At("oneVector", mu), omega), 2));
        Formula lhs = At("evaluation", At("finiteSecondIntegral", mu, p, w, F.Id("hW")), At("frequencyKernel", mu, v), omega);
        return Hypotheses(All("v", F.Id("Real"), At("AlmostEverywhere", p,
            All("omega", F.Id("Omega"), Eq(lhs, rhs)))), true);
    }
}
