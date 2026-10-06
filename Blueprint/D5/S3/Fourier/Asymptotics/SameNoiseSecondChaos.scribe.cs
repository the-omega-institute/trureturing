using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class SameNoiseSecondChaosDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric product-space kernels have a unique continuous centered-square integral on the same Gaussian noise.",
        H("Same-noise second integral"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("same-noise-diagonal-image"),
                DeclarationHandle.Create(Module + "secondIntegral_diagonal"),
                H("Original diagonal image"),
                StatementSource.FromAuthor(Hypotheses(All("f", HSpace,
                    Eq(At("apply", At("secondIntegral", F.Id("mu"), F.Id("P"), F.Id("W"), F.Id("hW")), At("diagonalKernel", F.Id("mu"), F.Id("f"))),
                        At("centeredSquare", F.Id("mu"), F.Id("P"), F.Id("W"), F.Id("hW"), F.Id("f")))), false)),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("The continuous second integral sends each actual diagonal kernel to the centered square of the same original W. The constant vector supplies the centered Y square in the finite-frequency remainder."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-noise-constant-representative"),
                DeclarationHandle.Create(Module + "oneVector_coe"),
                H("Constant vector representative"),
                StatementSource.FromAuthor(F.Disp(All("mu", At("Measure", F.Id("Real")), All("hfinite", At("IsFiniteMeasure", F.Id("mu")),
                    At("AEEq", At("coeFn", At("oneVector", F.Id("mu"))), Lambda("x", F.Id("Real"), F.D(1)), F.Id("mu")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("For every finite measure on the real line, the constant L2 vector has representative one almost everywhere. Its diagonal product therefore represents the constant spatial kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-noise-symmetric-density"),
                DeclarationHandle.Create(Module + "finiteKernelMap_dense"),
                H("Density in the actual symmetric space"),
                StatementSource.FromAuthor(DensityFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("For every finite measure mu on any measurable space X, the range of the finite diagonal-kernel map is dense in the fixed subspace of coordinate swap in L2(mu times mu). No normalization, positive mass or finite-dimensional restriction is imposed.")),
                    Paragraph(Text("A kernel orthogonal to every rank-one class has zero integral on every measurable rectangle. Rectangles generate the product sigma algebra; complements and disjoint countable unions preserve zero integrals. The kernel therefore vanishes almost everywhere. For a symmetric kernel, polarization of diagonal generators and invariance of inner products under swap reduce diagonal orthogonality to rank-one orthogonality. The symmetric subspace is closed and complete."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-noise-full-extension"),
                DeclarationHandle.Create(Module + "secondIntegral_characterization"),
                H("Continuous extension and characterization"),
                StatementSource.FromAuthor(ExtensionFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("Let P be a probability measure and W a fixed real linear isometry from L2(mu) to L2(P), with each W(f) having centered Gaussian law of variance ||f||^2. The second integral extends the finite coefficient assignment continuously to the full actual symmetric product-space L2 subspace.")),
                    Paragraph(Text("Every output has mean zero. For arbitrary symmetric kernels k and l its covariance is 2 inner(k,l), and its norm is sqrt(2)||k||. It is the unique continuous real linear map sending each diagonal kernel f(x)f(y) to the actual class W(f)^2-||f||^2. Density passes the finite Gram identity and mean to the full space. Every random variable uses the original W and P."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-noise-full-product"),
                DeclarationHandle.Create(Module + "secondIntegral_product"),
                H("Actual symmetrized products"),
                StatementSource.FromAuthor(ProductFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("For all f and g in L2(mu), symmetrizedKernel(f,g) has the product-measure representative (f(x)g(y)+g(x)f(y))/2. Its second integral has the almost-everywhere representative W(f)W(g)-inner(f,g) on the original probability space. Both conclusions include zero vectors, zero measure and linearly dependent vectors."))),
                DescribeRole.Theorem),
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
                    Paragraph(Text("The finite frequency identity agrees with the continuous extension on its actual finite-kernel input. Frequency integration and the singular logarithmic kernel require additional analytic statements; common continuous paths and process convergence require separate probability results."))),
                DescribeRole.Theorem))));

    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula At(string name, params Formula[] xs) => Call(name, xs);
    private static Formula Pow(Formula x, byte n) => new Formula.Power(x, F.D(n));
    private static Formula All(string name, Formula domain, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);

    private static Formula Lambda(string name, Formula domain, Formula body) =>
        F.Seq(F.Open, F.Id(name), F.Colon, domain, F.Mapsto, F.Sp, body, F.Close);
    private static Formula And(params Formula[] xs) =>
        xs.Aggregate((x, y) => new Formula.Logic(x, FormulaLogicOperator.And, y));
    private static Formula HSpace => At("Lp", F.Id("Real"), F.D(2), F.Id("mu"));
    private static Formula RSpace => At("Lp", F.Id("Real"), F.D(2), F.Id("P"));
    private static Formula KSpace => At("symmetricKernel", F.Id("mu"));

    private static Formula SpatialHypotheses(Formula body) => F.Disp(new Formula.BindMany(
        FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create("X"), F.Id("Type")),
         new Formula.BoundVariable(FormulaIdentifier.Create("SigmaX"), At("MeasurableSpace", F.Id("X"))),
         new Formula.BoundVariable(FormulaIdentifier.Create("mu"), At("Measure", F.Id("X"))),
         new Formula.BoundVariable(FormulaIdentifier.Create("hfinite"), At("IsFiniteMeasure", F.Id("mu")))], body));

    private static Formula Hypotheses(Formula body, bool frequency)
    {
        Formula mu = F.Id("mu"), p = F.Id("P"), w = F.Id("W");
        Formula laws = All("f", HSpace, At("HasLaw", At("representative", At("apply", w, F.Id("f"))),
            At("gaussianReal", F.D(0), At("toNNReal", Pow(At("norm", F.Id("f")), 2))), p));
        var binders = new List<Formula.BoundVariable>();
        if (!frequency)
        {
            binders.Add(new(FormulaIdentifier.Create("X"), F.Id("Type")));
            binders.Add(new(FormulaIdentifier.Create("SigmaX"), At("MeasurableSpace", F.Id("X"))));
        }
        binders.Add(new(FormulaIdentifier.Create("mu"), At("Measure", frequency ? F.Id("Real") : F.Id("X"))));
        binders.Add(new(FormulaIdentifier.Create("hfinite"), At("IsFiniteMeasure", mu)));
        binders.Add(new(FormulaIdentifier.Create("Omega"), F.Id("Type")));
        binders.Add(new(FormulaIdentifier.Create("SigmaOmega"), At("MeasurableSpace", F.Id("Omega"))));
        binders.Add(new(FormulaIdentifier.Create("P"), At("Measure", F.Id("Omega"))));
        binders.Add(new(FormulaIdentifier.Create("hprob"), At("IsProbabilityMeasure", p)));
        binders.Add(new(FormulaIdentifier.Create("W"), At("LinearIsometry", F.Id("Real"), HSpace, RSpace)));
        binders.Add(new(FormulaIdentifier.Create("hW"), laws));
        return F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders], body));
    }

    private static Formula DensityFormula() => SpatialHypotheses(
        At("DenseRange", At("finiteKernelMap", F.Id("mu"))));

    private static Formula ExtensionFormula()
    {
        Formula mu = F.Id("mu"), p = F.Id("P"), w = F.Id("W"), law = F.Id("hW");
        Formula integral = At("secondIntegral", mu, p, w, law);
        Formula image(string k) => At("apply", integral, F.Id(k));
        Formula mean = All("k", KSpace, Eq(At("Integral", p,
            Lambda("omega", F.Id("Omega"), At("evaluation", image("k"), F.Id("omega")))), F.D(0)));
        Formula covariance = All("k", KSpace, All("l", KSpace,
            Eq(At("inner", image("k"), image("l")), Multiply(F.D(2), At("inner", F.Id("k"), F.Id("l"))))));
        Formula norm = All("k", KSpace, Eq(At("norm", image("k")),
            Multiply(At("sqrt", F.D(2)), At("norm", F.Id("k")))));
        Formula agreement = All("f", HSpace, Eq(At("apply", F.Id("J"), At("diagonalKernel", mu, F.Id("f"))),
            At("centeredSquare", mu, p, w, law, F.Id("f"))));
        Formula unique = All("J", At("ContinuousLinearMap", F.Id("Real"), KSpace, RSpace),
            new Formula.Logic(agreement, FormulaLogicOperator.Implies, Eq(F.Id("J"), integral)));
        return Hypotheses(And(mean, covariance, norm, unique), false);
    }

    private static Formula ProductFormula()
    {
        Formula mu = F.Id("mu"), p = F.Id("P"), w = F.Id("W"), law = F.Id("hW"),
            f = F.Id("f"), g = F.Id("g"), z = F.Id("z"), omega = F.Id("omega");
        Formula kernel = At("symmetrizedKernel", mu, f, g);
        Formula spatial = At("AlmostEverywhere", At("prod", mu, mu), Lambda("z", At("Prod", F.Id("X"), F.Id("X")),
            Eq(At("evaluation", At("val", kernel), z), new Formula.Fraction(F.Seq(
                Multiply(At("evaluation", f, At("fst", z)), At("evaluation", g, At("snd", z))), F.Plus,
                Multiply(At("evaluation", g, At("fst", z)), At("evaluation", f, At("snd", z)))), F.D(2)))));
        Formula noise = At("AlmostEverywhere", p, Lambda("omega", F.Id("Omega"),
            Eq(At("evaluation", At("apply", At("secondIntegral", mu, p, w, law), kernel), omega),
                F.Seq(Multiply(At("evaluation", At("apply", w, f), omega),
                    At("evaluation", At("apply", w, g), omega)), F.Minus, At("inner", f, g)))));
        return Hypotheses(All("f", HSpace, All("g", HSpace, And(spatial, noise))), false);
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
            Lambda("omega", F.Id("Omega"), Eq(lhs, rhs)))), true);
    }
}
