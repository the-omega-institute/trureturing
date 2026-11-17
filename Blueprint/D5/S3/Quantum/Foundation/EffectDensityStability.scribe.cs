using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class EffectDensityStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform approximate effect additivity yields one density with explicit dimension-dependent error.",
        H("Quantitative density stability on all effects"),
        Blocks(
            Paragraph(Text("In the formulas, Mat(d) is Matrix(Fin(d), Fin(d), C), Id(d) is its identity and Tr is the complex trace. The symbol i in roman type is the complex imaginary unit; italic indices lie in Fin(d). The real and complex embeddings, real and complex, are explicit where needed. Dots mean scalar action or matrix multiplication according to type. The functions fst and snd are the two pair projections, and ite(Q,u,v) is u if Q holds and v otherwise. The matrix single(i,j,z) has entry z only at (i,j); singleVector(i,z) has coordinate z only at i. The matrix vecMulVec(u,v) has entry u(r)v(s), and star conjugates a scalar or each vector coordinate. The function diagonal(v) places v on the diagonal. All sums run over the displayed finite type. The generic sum identities retain arbitrary universes and the anonymous algebraic instance assumptions.")),
            Paragraph(Text("Let d>=1, epsilon>=0 and p be an arbitrary total real function on actual Matrix (Fin d) (Fin d) Complex. An effect E has E.PosSemidef and (1-E).PosSemidef. Assume nonnegativity on every effect, p(identity)=1 and absolute binary defect at most epsilon for all positive semidefinite pairs with effect-valued sum.")),
            Paragraph(Text("Diagonal probes and real and imaginary pair probes give d squared positive matrices. Their total is at most (2*d-1) times the identity and every effect coordinate has absolute value at most 2*d-1. The signed-family estimate therefore gives a Hermitian candidate error eta=(2*d-1)^2*(6*d^2+1)*epsilon. The exact coordinate trace formula identifies the same candidate on every Hermitian matrix.")),
            Paragraph(Text("Nonnegativity and normalization give the two premises of uniform density repair. Its 3*eta correction combines with the candidate error to give 4*(2*d-1)^2*(6*d^2+1)*epsilon for one positive semidefinite rho with complex trace exactly one, simultaneously for every actual effect. This quantitative argument is the finite positive-coordinate construction with bounded interval stability and spectral repair.")),
            Paragraph(Text("Busch supplies the exact all-effect representation background. The quantitative estimate uses the global hypotheses stated here; finite observations alone do not establish them. No optimality, positive-error uniqueness or physical realization is asserted.")),
            Describe.Lean(
                DescribeId.Create("diagonal-probe"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.diagonalProbe"),
                H("diagonalProbe"),
                StatementSource.FromAuthor(Statement("diagonalProbe")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The diagonal probe is the matrix with a single one at the indicated diagonal coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("real-probe"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.realProbe"),
                H("realProbe"),
                StatementSource.FromAuthor(Statement("realProbe")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The real pair probe is one half of the outer product of e_i+e_j with its conjugate; effect claims below retain the distinct-index premise."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("imaginary-probe"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.imaginaryProbe"),
                H("imaginaryProbe"),
                StatementSource.FromAuthor(Statement("imaginaryProbe")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The imaginary pair probe is one half of the outer product of e_i+I*e_j with its conjugate, fixing the negative imaginary sign in its upper entry."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("upper-entry"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.upperEntry"),
                H("upperEntry"),
                StatementSource.FromAuthor(Statement("upperEntry")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The upper candidate entry is formed from actual values on the real and imaginary pair probes and the mean of the two diagonal values."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("candidate"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.candidate"),
                H("candidate"),
                StatementSource.FromAuthor(Statement("candidate")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every arbitrary real function on actual matrices, the candidate uses its diagonal probe values, the specified upper entries and conjugate lower entries."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("candidate-hermitian"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.candidate_hermitian"),
                H("candidate hermitian"),
                StatementSource.FromAuthor(Statement("candidate_hermitian")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The concrete candidate is Hermitian for every real function p and every natural dimension, without any positivity, normalization or additivity hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-minus"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.realMinus"),
                H("realMinus"),
                StatementSource.FromAuthor(Statement("realMinus")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The real complementary pair matrix is one half of the outer product of e_i-e_j with its conjugate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("imaginary-minus"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.imaginaryMinus"),
                H("imaginaryMinus"),
                StatementSource.FromAuthor(Statement("imaginaryMinus")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The imaginary complementary pair matrix is one half of the outer product of e_i-I*e_j with its conjugate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("diagonal-eq"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.diagonal_eq"),
                H("diagonal eq"),
                StatementSource.FromAuthor(Statement("diagonal_eq")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each diagonal probe is exactly the diagonal matrix of the corresponding coordinate indicator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonal-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.diagonal_effect"),
                H("diagonal effect"),
                StatementSource.FromAuthor(Statement("diagonal_effect")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every diagonal probe is an actual effect in every natural dimension for which its index exists."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pair-diagonal-le"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.pair_diagonal_le"),
                H("pair diagonal le"),
                StatementSource.FromAuthor(Statement("pair_diagonal_le")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the sum of the two diagonal probes is at most the identity in native matrix order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-complement"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.real_complement"),
                H("real complement"),
                StatementSource.FromAuthor(Statement("real_complement")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the sum of the diagonal probes minus the real pair probe equals its specified real complementary outer product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("imaginary-complement"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_complement"),
                H("imaginary complement"),
                StatementSource.FromAuthor(Statement("imaginary_complement")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the sum of the diagonal probes minus the imaginary pair probe equals its specified imaginary complementary outer product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-le-pair"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.real_le_pair"),
                H("real le pair"),
                StatementSource.FromAuthor(Statement("real_le_pair")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the real pair probe is bounded above by the sum of its diagonal probes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("imaginary-le-pair"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_le_pair"),
                H("imaginary le pair"),
                StatementSource.FromAuthor(Statement("imaginary_le_pair")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the imaginary pair probe is bounded above by the sum of its diagonal probes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.real_effect"),
                H("real effect"),
                StatementSource.FromAuthor(Statement("real_effect")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the real pair probe and its identity complement are positive semidefinite."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("imaginary-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_effect"),
                H("imaginary effect"),
                StatementSource.FromAuthor(Statement("imaginary_effect")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the imaginary pair probe and its identity complement are positive semidefinite."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("entry-norm-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.entry_norm_bound"),
                H("entry norm bound"),
                StatementSource.FromAuthor(Statement("entry_norm_bound")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every complex entry of every actual effect has complex norm at most one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("probe"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.probe"),
                H("probe"),
                StatementSource.FromAuthor(Statement("probe")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The index pair selects a diagonal probe on the diagonal, a real pair probe above it and an imaginary pair probe below it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("probe-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.probe_effect"),
                H("probe effect"),
                StatementSource.FromAuthor(Statement("probe_effect")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every member of this concrete indexed probe family is an actual effect."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("probe-card"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.probe_card"),
                H("probe card"),
                StatementSource.FromAuthor(Statement("probe_card")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In every natural dimension the finite pair-index type has exactly d^2 members."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("majorant"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.majorant"),
                H("majorant"),
                StatementSource.FromAuthor(Statement("majorant")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The majorant is the sum of the two indicated diagonal probes, with one duplicate removed on the diagonal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("probe-le-majorant"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.probe_le_majorant"),
                H("probe le majorant"),
                StatementSource.FromAuthor(Statement("probe_le_majorant")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every concrete probe is bounded above by its stated diagonal majorant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonal-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.diagonal_sum"),
                H("diagonal sum"),
                StatementSource.FromAuthor(Statement("diagonal_sum")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The sum of all diagonal probes is the actual identity matrix, including the empty-dimensional identity convention."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("triangular-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.triangular_sum"),
                H("triangular sum"),
                StatementSource.FromAuthor(Statement("triangular_sum")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any finite linearly ordered index type and any additive commutative monoid, the double sum splits into its diagonal sum and paired strict-upper sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("incident-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.incident_sum"),
                H("incident sum"),
                StatementSource.FromAuthor(Statement("incident_sum")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any finite index type and any real module with additive commutative monoid structure, the sum of incident scalar weights on the indexed vectors equals the double sum of pair weights on the corresponding vector sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.coordinate"),
                H("coordinate"),
                StatementSource.FromAuthor(Statement("coordinate")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The concrete real Hermitian coordinates use twice the real upper entry, minus twice its imaginary part, and the stated diagonal incident corrections."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("offdiag-term"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.offdiagTerm"),
                H("offdiagTerm"),
                StatementSource.FromAuthor(Statement("offdiagTerm")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each upper pair contributes its real and imaginary probe multiples with the diagonal correction subtracted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("offdiag-identity"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.offdiag_identity"),
                H("offdiag identity"),
                StatementSource.FromAuthor(Statement("offdiag_identity")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any actual complex matrix and distinct indices the corrected pair contribution is exactly its upper matrix unit plus the conjugate lower matrix unit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("upper-correction"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.upperCorrection"),
                H("upperCorrection"),
                StatementSource.FromAuthor(Statement("upperCorrection")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The correction is the real part minus the imaginary part of an upper entry, and zero elsewhere."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coordinate-diagonal"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_diagonal"),
                H("coordinate diagonal"),
                StatementSource.FromAuthor(Statement("coordinate_diagonal")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The diagonal coordinate subtracts the sum of both incident upper corrections from the real diagonal entry, for every actual complex matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate-pair"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_pair"),
                H("coordinate pair"),
                StatementSource.FromAuthor(Statement("coordinate_pair")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The two coordinates and probes of an upper pair split into the off-diagonal contribution and its diagonal correction, with the displayed conditional retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate-split"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_split"),
                H("coordinate split"),
                StatementSource.FromAuthor(Statement("coordinate_split")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every actual complex matrix the complete probe sum splits into its real diagonal contribution and the sum of corrected upper-pair contributions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate-expansion"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_expansion"),
                H("coordinate expansion"),
                StatementSource.FromAuthor(Statement("coordinate_expansion")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every actual Hermitian matrix is exactly the real linear combination of the concrete probes given by its coordinates; all natural dimensions are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-probe-decomp"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.real_probe_decomp"),
                H("real probe decomp"),
                StatementSource.FromAuthor(Statement("real_probe_decomp")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the real pair probe is one half of the sum of its four specified matrix units."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("imaginary-probe-decomp"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_probe_decomp"),
                H("imaginary probe decomp"),
                StatementSource.FromAuthor(Statement("imaginary_probe_decomp")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the imaginary pair probe is one half of the four specified matrix units, with upper coefficient -I and lower coefficient I."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("trace-single-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.trace_single_sum"),
                H("trace single sum"),
                StatementSource.FromAuthor(Statement("trace_single_sum")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any actual complex matrix C and complex scalar a, the complex trace of C times the indicated matrix unit is exactly a*C(j,i)."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("trace-real-formula"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.trace_real_formula"),
                H("trace real formula"),
                StatementSource.FromAuthor(Statement("trace_real_formula")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every actual complex C and distinct indices, its real trace pairing with the real pair probe is the stated mean of four real entries, without a Hermiticity hypothesis."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("trace-imaginary-formula"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.trace_imaginary_formula"),
                H("trace imaginary formula"),
                StatementSource.FromAuthor(Statement("trace_imaginary_formula")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every actual complex C and distinct indices, its real trace pairing with the imaginary pair probe is the stated combination of diagonal real parts and off-diagonal imaginary parts, without a Hermiticity hypothesis."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("probe-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.probe_trace"),
                H("probe trace"),
                StatementSource.FromAuthor(Statement("probe_trace")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every arbitrary real p the concrete Hermitian candidate reproduces p exactly on every probe through the real part of the actual complex trace."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_trace"),
                H("coordinate trace"),
                StatementSource.FromAuthor(Statement("coordinate_trace")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every arbitrary real p and every actual Hermitian H, the real part of the complex trace of candidate(p)*H equals the complete coordinate-weighted sum of p on the concrete probes. No probability premises on p are assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("majorant-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.majorant_sum"),
                H("majorant sum"),
                StatementSource.FromAuthor(Statement("majorant_sum")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In every natural dimension the total diagonal majorant equals (2*d-1) times the actual identity, with d interpreted in the reals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("probe-sum-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.probe_sum_bound"),
                H("probe sum bound"),
                StatementSource.FromAuthor(Statement("probe_sum_bound")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In every natural dimension the total concrete probe family is at most (2*d-1) times the actual identity in native matrix order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_bound"),
                H("coordinate bound"),
                StatementSource.FromAuthor(Statement("coordinate_bound")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every d>=1 and every actual effect, every concrete real coordinate has absolute value at most 2*d-1, including dimension one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("candidate-error"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.candidate_error"),
                H("candidate error"),
                StatementSource.FromAuthor(Statement("candidate_error")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every d>=1 and epsilon>=0, global effect nonnegativity, identity normalization and binary defect at most epsilon bound the error from p to the concrete candidate on every actual effect by (2*d-1)^2*(6*d^2+1)*epsilon."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("approximate-effect-density"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.approximate_effect_density"),
                H("approximate effect density"),
                StatementSource.FromAuthor(Statement("approximate_effect_density")),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/busch2003effectprobabilities")),
                Blocks(
                    Paragraph(Text("For every natural d>=1, every real epsilon>=0 and every arbitrary real function p on actual complex d by d matrices, assume p is nonnegative on every actual effect, p(identity)=1, and absolute binary additive defect at most epsilon for all positive semidefinite E,F whose sum is an effect. There exists ONE actual positive semidefinite complex matrix rho with COMPLEX trace rho=1, such that for EVERY actual effect E the absolute difference between p(E) and Re(trace(rho*E)) is at most 4*(2*d-1)^2*(6*d^2+1)*epsilon, with d interpreted in the reals. The density is chosen before E. Epsilon zero and dimension one are included. No continuity, measurability, p(0)=0, commutativity, rank, small-error, supplied-coordinate, supplied-density or finite-sample premise is imposed."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, P(Seq(variable, Colon, Sp, type)), Comma, Sp, P(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, P(Seq(variable, Colon, Sp, type)), Comma, Sp, P(body));
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(P(clauses[index]));
        }
        return Seq([.. items]);
    }
    private static Formula Imp(Formula premise, Formula result) => Seq(P(premise), Sp, Implies, Sp, P(result));
    private static Formula EqTo(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Le(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula LtTo(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula Ne(Formula left, Formula right) => Seq(left, Sp, Neq, Sp, right);
    private static Formula Add(Formula left, Formula right) => P(Seq(left, Plus, right));
    private static Formula Sub(Formula left, Formula right) => P(Seq(left, Minus, right));
    private static Formula Mul(Formula left, Formula right) => P(Seq(left, Sp, Cdot, Sp, right));
    private static Formula Scale(Formula scalar, Formula value) => P(Seq(scalar, Sp, Cdot, Sp, value));
    private static Formula Pow(Formula value, Formula exponent) => Seq(P(value), Caret, Grp(exponent));
    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert, Sp);
    private static Formula At(Formula function, params Formula[] arguments) =>
        Seq(function, P(Seq(JoinArguments(arguments))));
    private static Formula[] JoinArguments(Formula[] arguments)
    {
        var items = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        return [.. items];
    }
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(variable, Colon, Sp, type)), Sp, P(body));
    private static Formula Arrow(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Pair(Formula left, Formula right) => P(Seq(left, Comma, Sp, right));
    private static Formula Product(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula Lambda(Formula variable, Formula type, Formula body) =>
        P(Seq(P(Seq(variable, Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Inst(string name, Formula type, Formula body) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp, P(body));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula dimension) => Call("Fin", dimension);
    private static Formula Mat(Formula dimension) => Call("Mat", dimension);
    private static Formula Identity(Formula dimension) => Call("Id", dimension);
    private static Formula Psd(Formula value) => Call("PosSemidef", value);
    private static Formula Hermitian(Formula value) => Call("IsHermitian", value);
    private static Formula Effect(Formula value, Formula dimension) => And(Psd(value), Psd(Sub(Identity(dimension), value)));
    private static Formula Trace(Formula value) => Call("Tr", value);
    private static Formula RealPart(Formula value) => Seq(Re, Sp, P(value));
    private static Formula Born(Formula density, Formula value) => RealPart(Trace(Mul(density, value)));
    private static Formula Density(Formula value) => And(Psd(value), EqTo(Trace(value), D(1)));

    private static Formula Statement(string name)
    {
        Formula d = V("d"), p = V("p"), e = V("E"), c = V("C"), i = V("i"), j = V("j"),
            k = V("k"), a = V("a"), h = V("H"), q = V("q"), vectors = V("D"),
            index = V("J"), target = V("A"), f = V("f"), eps = Varepsilon;
        Formula matrix = Mat(d), fin = Fin(d), pairs = Product(fin, fin), imaginary = Seq(Mathrm, Grp(V("i")));
        Formula first = Call("fst", a), second = Call("snd", a);
        Formula Diagonal(Formula x) => Call("diagonalProbe", x);
        Formula Probe(Formula x) => Call("probe", x);
        Formula RealProbe(Formula x, Formula y) => Call("realProbe", x, y);
        Formula ImagProbe(Formula x, Formula y) => Call("imaginaryProbe", x, y);
        Formula Upper(Formula x, Formula y) => Call("upperEntry", p, x, y);
        Formula Candidate() => Call("candidate", p);
        Formula Entry(Formula x, Formula y) => At(e, x, y);
        Formula ReEntry(Formula x, Formula y) => RealPart(Entry(x, y));
        Formula ImEntry(Formula x, Formula y) => Call("Im", Entry(x, y));
        Formula Coord(Formula x) => Call("coordinate", e, x);
        Formula Off(Formula x, Formula y) => Call("offdiagTerm", e, x, y);
        Formula Correction(Formula x, Formula y) => Call("upperCorrection", e, x, y);
        Formula DiagonalPair() => Add(Diagonal(i), Diagonal(j));
        Formula Dims(Formula body) => All(d, Nat, body);
        Formula IJ(Formula body) => Dims(All(i, fin, All(j, fin, body)));
        Formula Distinct(Formula body) => IJ(Imp(Ne(i, j), body));
        Formula InputE(Formula body) => Dims(All(e, matrix, body));
        Formula InputP(Formula body) => Dims(All(p, Arrow(matrix, Real), body));
        Formula InputPair(Formula body) => Dims(All(a, pairs, body));
        Formula EffectE(Formula body) => InputE(Imp(Effect(e, d), body));
        Formula Single(Formula x, Formula y, Formula value) => Call("single", x, y, value);
        Formula Half(Formula value) => Seq(Frac, Grp(value), Grp(D(2)));
        Formula Vector(Formula x, Formula scalar) => Call("singleVector", x, scalar);
        Formula Outer(Formula vector) => Scale(Call("complex", Half(D(1))),
            Call("vecMulVec", vector, Call("star", vector)));
        Formula SignedVector(bool imag, bool minus) => minus
            ? Sub(Vector(i, D(1)), Vector(j, imag ? imaginary : D(1)))
            : Add(Vector(i, D(1)), Vector(j, imag ? imaginary : D(1)));
        Formula CoordinateSum() => SumOver(a, pairs, Scale(Coord(a), Probe(a)));
        Formula UpperSum() => SumOver(i, fin, SumOver(j, fin, Call("ite", LtTo(i, j), Off(i, j), D(0))));
        Formula Mean() => Half(Add(At(p, Diagonal(i)), At(p, Diagonal(j))));
        Formula DoubleSum(Formula domain, Formula body) => SumOver(i, domain, SumOver(j, domain, body));
        Formula Generic(Formula body, bool ordered) => All(index, Call("Type"), All(target, Call("Type"),
            Inst("Fintype", index, ordered
                ? Inst("LinearOrder", index, Inst("AddCommMonoid", target, body))
                : Inst("AddCommMonoid", target,
                    Seq(OpenBracket, Call("Module", Real, target), CloseBracket, Sp, P(body))))));
        Formula TraceInput(Formula body) => Dims(All(c, matrix, All(i, fin, All(j, fin, Imp(Ne(i, j), body)))));
        Formula DimensionBound() => Sub(Mul(D(2), Call("real", d)), D(1));
        Formula ErrorConstant() => Mul(Mul(Pow(DimensionBound(), D(2)),
            Add(Mul(D(6), Pow(Call("real", d), D(2))), D(1))), eps);
        Formula GlobalPremises()
        {
            Formula x = V("X"), y = V("Y");
            return And(Le(D(0), eps),
                All(x, matrix, Imp(Effect(x, d), Le(D(0), At(p, x)))),
                EqTo(At(p, Identity(d)), D(1)),
                All(x, matrix, All(y, matrix, Imp(And(Psd(x), Psd(y), Effect(Add(x, y), d)),
                    Le(Abs(Sub(Sub(At(p, Add(x, y)), At(p, x)), At(p, y))), eps)))));
        }
        Formula StabilityInput(Formula body) => Dims(Imp(Le(D(1), d),
            All(eps, Real, All(p, Arrow(matrix, Real), Imp(GlobalPremises(), body)))));
        Formula body = name switch
        {
            "diagonalProbe" => Dims(All(i, fin, EqTo(Diagonal(i), Single(i, i, D(1))))),
            "realProbe" => IJ(EqTo(RealProbe(i, j), Outer(SignedVector(false, false)))),
            "imaginaryProbe" => IJ(EqTo(ImagProbe(i, j), Outer(SignedVector(true, false)))),
            "upperEntry" => InputP(All(i, fin, All(j, fin, EqTo(Upper(i, j),
                Add(Call("complex", Sub(At(p, RealProbe(i, j)), Mean())),
                    Mul(imaginary, Call("complex", Sub(Mean(), At(p, ImagProbe(i, j)))))))))),
            "candidate" => InputP(All(i, fin, All(j, fin, EqTo(At(Candidate(), i, j),
                Call("ite", EqTo(i, j), Call("complex", At(p, Diagonal(i))),
                    Call("ite", LtTo(i, j), Upper(i, j), Call("star", Upper(j, i)))))))),
            "candidate_hermitian" => InputP(Hermitian(Candidate())),
            "realMinus" => IJ(EqTo(Call("realMinus", i, j), Outer(SignedVector(false, true)))),
            "imaginaryMinus" => IJ(EqTo(Call("imaginaryMinus", i, j), Outer(SignedVector(true, true)))),
            "diagonal_eq" => Dims(All(i, fin, EqTo(Diagonal(i), Call("diagonal",
                Lambda(k, fin, Call("ite", EqTo(k, i), D(1), D(0))))))),
            "diagonal_effect" => Dims(All(i, fin, Effect(Diagonal(i), d))),
            "pair_diagonal_le" => Distinct(Le(DiagonalPair(), Identity(d))),
            "real_complement" => Distinct(EqTo(Sub(DiagonalPair(), RealProbe(i, j)), Call("realMinus", i, j))),
            "imaginary_complement" => Distinct(EqTo(Sub(DiagonalPair(), ImagProbe(i, j)), Call("imaginaryMinus", i, j))),
            "real_le_pair" => Distinct(Le(RealProbe(i, j), DiagonalPair())),
            "imaginary_le_pair" => Distinct(Le(ImagProbe(i, j), DiagonalPair())),
            "real_effect" => Distinct(Effect(RealProbe(i, j), d)),
            "imaginary_effect" => Distinct(Effect(ImagProbe(i, j), d)),
            "entry_norm_bound" => EffectE(All(i, fin, All(j, fin, Le(Call("norm", Entry(i, j)), D(1))))),
            "probe" => InputPair(EqTo(Probe(a), Call("ite", EqTo(first, second), Diagonal(first),
                Call("ite", LtTo(first, second), RealProbe(first, second), ImagProbe(second, first))))),
            "probe_effect" => InputPair(Effect(Probe(a), d)),
            "probe_card" => Dims(EqTo(Call("card", pairs), Pow(d, D(2)))),
            "majorant" => InputPair(EqTo(Call("majorant", a),
                Sub(Add(Diagonal(first), Diagonal(second)), Call("ite", EqTo(first, second), Diagonal(first), D(0))))),
            "probe_le_majorant" => InputPair(Le(Probe(a), Call("majorant", a))),
            "diagonal_sum" => Dims(EqTo(SumOver(i, fin, Diagonal(i)), Identity(d))),
            "triangular_sum" => Generic(All(f, Arrow(index, Arrow(index, target)),
                EqTo(DoubleSum(index, At(f, i, j)), Add(SumOver(i, index, At(f, i, i)),
                    DoubleSum(index, Call("ite", LtTo(i, j), Add(At(f, i, j), At(f, j, i)), D(0)))))), true),
            "incident_sum" => Generic(All(q, Arrow(index, Arrow(index, Real)), All(vectors, Arrow(index, target),
                EqTo(SumOver(i, index, Scale(SumOver(j, index, Add(At(q, i, j), At(q, j, i))), At(vectors, i))),
                    DoubleSum(index, Scale(At(q, i, j), Add(At(vectors, i), At(vectors, j))))))), false),
            "coordinate" => InputE(All(a, pairs, EqTo(Coord(a),
                Call("ite", EqTo(first, second), Sub(ReEntry(first, first), SumOver(k, fin,
                    Call("ite", LtTo(first, k), Sub(ReEntry(first, k), ImEntry(first, k)),
                        Call("ite", LtTo(k, first), Sub(ReEntry(k, first), ImEntry(k, first)), D(0))))),
                    Call("ite", LtTo(first, second), Mul(D(2), ReEntry(first, second)),
                        Mul(Seq(Minus, D(2)), ImEntry(second, first))))))),
            "offdiagTerm" => InputE(All(i, fin, All(j, fin, EqTo(Off(i, j),
                Sub(Add(Scale(Mul(D(2), ReEntry(i, j)), RealProbe(i, j)),
                    Scale(Mul(Seq(Minus, D(2)), ImEntry(i, j)), ImagProbe(i, j))),
                    Scale(Sub(ReEntry(i, j), ImEntry(i, j)), DiagonalPair())))))),
            "offdiag_identity" => InputE(All(i, fin, All(j, fin, Imp(Ne(i, j), EqTo(Off(i, j),
                Add(Single(i, j, Entry(i, j)), Single(j, i, Call("star", Entry(i, j))))))))),
            "upperCorrection" => InputE(All(i, fin, All(j, fin, EqTo(Correction(i, j),
                Call("ite", LtTo(i, j), Sub(ReEntry(i, j), ImEntry(i, j)), D(0)))))),
            "coordinate_diagonal" => InputE(All(i, fin, EqTo(Coord(Pair(i, i)),
                Sub(ReEntry(i, i), SumOver(j, fin, Add(Correction(i, j), Correction(j, i))))))),
            "coordinate_pair" => InputE(All(i, fin, All(j, fin, EqTo(
                Call("ite", LtTo(i, j), Add(Scale(Coord(Pair(i, j)), Probe(Pair(i, j))),
                    Scale(Coord(Pair(j, i)), Probe(Pair(j, i)))), D(0)),
                Add(Call("ite", LtTo(i, j), Off(i, j), D(0)), Scale(Correction(i, j), DiagonalPair())))))),
            "coordinate_split" => InputE(EqTo(CoordinateSum(),
                Add(SumOver(i, fin, Scale(ReEntry(i, i), Diagonal(i))), UpperSum()))),
            "coordinate_expansion" => InputE(Imp(Hermitian(e), EqTo(CoordinateSum(), e))),
            "real_probe_decomp" => Distinct(EqTo(RealProbe(i, j), Scale(Call("complex", Half(D(1))),
                Add(Add(Add(Single(i, i, D(1)), Single(i, j, D(1))), Single(j, i, D(1))), Single(j, j, D(1)))))),
            "imaginary_probe_decomp" => Distinct(EqTo(ImagProbe(i, j), Scale(Call("complex", Half(D(1))),
                Add(Add(Add(Single(i, i, D(1)), Single(i, j, Seq(Minus, imaginary))),
                    Single(j, i, imaginary)), Single(j, j, D(1)))))),
            "trace_single_sum" => Dims(All(c, matrix, All(i, fin, All(j, fin, All(a, Complex,
                EqTo(Trace(Mul(c, Single(i, j, a))), Mul(a, At(c, j, i)))))))),
            "trace_real_formula" => TraceInput(EqTo(Born(c, RealProbe(i, j)),
                Half(Add(Add(Add(RealPart(At(c, i, i)), RealPart(At(c, j, j))),
                    RealPart(At(c, i, j))), RealPart(At(c, j, i)))))),
            "trace_imaginary_formula" => TraceInput(EqTo(Born(c, ImagProbe(i, j)),
                Half(Sub(Add(Add(RealPart(At(c, i, i)), RealPart(At(c, j, j))),
                    Call("Im", At(c, j, i))), Call("Im", At(c, i, j)))))),
            "probe_trace" => InputP(All(a, pairs, EqTo(Born(Candidate(), Probe(a)), At(p, Probe(a))))),
            "coordinate_trace" => InputP(All(h, matrix, Imp(Hermitian(h),
                EqTo(Born(Candidate(), h), SumOver(a, pairs, Mul(Call("coordinate", h, a), At(p, Probe(a)))))))),
            "majorant_sum" => Dims(EqTo(SumOver(a, pairs, Call("majorant", a)), Scale(DimensionBound(), Identity(d)))),
            "probe_sum_bound" => Dims(Le(SumOver(a, pairs, Probe(a)), Scale(DimensionBound(), Identity(d)))),
            "coordinate_bound" => Dims(Imp(Le(D(1), d), All(e, matrix, Imp(Effect(e, d),
                All(a, pairs, Le(Abs(Coord(a)), DimensionBound())))))),
            "candidate_error" => StabilityInput(All(e, matrix, Imp(Effect(e, d),
                Le(Abs(Sub(At(p, e), Born(Candidate(), e))), ErrorConstant())))),
            "approximate_effect_density" => StabilityInput(Some(Rho, matrix, And(Density(Rho),
                All(e, matrix, Imp(Effect(e, d), Le(Abs(Sub(At(p, e), Born(Rho, e))), Mul(D(4), ErrorConstant()))))))),
            _ => throw new ArgumentOutOfRangeException(nameof(name))
        };
        return Disp(body);
    }
}
