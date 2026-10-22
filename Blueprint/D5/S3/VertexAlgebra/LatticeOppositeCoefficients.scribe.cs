using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeOppositeCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeOppositeCoefficients.";

    private static DocumentBlock.Describe Entry(string name, string title, string text, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("lattice-opposite-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite actual opposite coefficients retain every Sugawara descendant and the indispensable current zero correction.",
        H("Finite Opposite Coefficients on the Actual Matter Carrier"),
        Blocks(
            Paragraph(Text("Write L1=sugawaraMode(D,H,1), Y=LatticeAllStateField.Y and A_i(q)=neutralMode(D,i,q). "
                + "For an integer h the opposite coefficient is paritySign(h) times the sum over j=0,...,N(a) of (j!)^-1 Y(L1^j a)[2h-n-j-2]. "
                + "This is a family of endomorphism coefficients, not a claim that the opposite family is a native lower-truncated VertexOperator. "
                + "The algebraic definition accepts every integer h; its conformal interpretation uses a in the actual grade h.")),
            Paragraph(Text("Local nilpotence and cutoff independence require no inverse-Gram equations. "
                + "The actual normalized current commutator and all conformal weight statements retain both H*gramComplex(D)=1 and gramComplex(D)*H=1. "
                + "Weights may be negative and the state may have any finite charge and monomial support. No form, adjoint, unitarity or positivity premise occurs.")),
            Paragraph(Text("The upstream factorial identities give choose(k+ell,ell)*(r)_ell/(k+ell)!=choose(r,ell)/k!; "
                + "the ell=r term is the original current-zero action. For an actual state a of grade h, each actual L1^j a has grade h-j. "
                + "Applying actual_mode_grade to Y(L1^j a)[2h-n-j-2]b puts every summand in grade k-h+n+1 when b has grade k; "
                + "finite addition therefore gives the same grade for O_a(n)b. This is an application of the original grade and factorial suppliers, not a new positivity statement.")),
            Entry("oppositeTerm", "A factorial-weighted actual descendant mode", "The j-th term uses the original L1 iterate, the original reconstructed Y and the exact reflected integer index.", DescribeRole.Definition),
            Entry("oppositeCoeff", "Finite opposite coefficient", "The sum truncates only at the true native oscillator bound N(a).", DescribeRole.Definition),
            Entry("opposite_cutoff", "Independence of every larger cutoff", "Every cutoff strictly larger than N(a) gives exactly the same endomorphism coefficient; each extra actual descendant is zero."),
            Entry("opposite_terms_finite", "Finite descendant support", "The actual descendant-term family has finite support in j, uniformly for its endomorphism value at a fixed n."),
            Entry("opposite_cutoff_apply", "Actual pointwise cutoff expression", "Every cutoff larger than N(a) gives the same original coefficient action on each tested vector; the finite sum uses exact factorials and reflected indices."),
            Entry("opposite_finsum", "Finite-support sum expression", "The chosen finite cutoff agrees with the supported natural-index finsum."),
            Entry("zero_current_correction", "The exact current zero correction", "Y(b)[q] A_i(0)+Y(A_i(0)b)[q]=A_i(0)Y(b)[q]. The original actual mode_commutator at p=0 proves the identity; A_i(0) is not silently discarded on charged states."),
            Entry("current_negative_insertion", "Actual negative-current reconstruction", "For r=degree+1, Y(A_i(-r)b)[n]v equals sum_t choose(t+r-1,r-1) A_i(-t-r)Y(b)[n+t]v plus (-1)^(r-1) sum_s choose(s+r-1,r-1)Y(b)[n-s-r]A_i(s)v. Both sums have actual pointwise finite support. This is the original residue reconstruction, not a globally finite End-valued infinite sum."),
            Entry("one_pow_current_insertion", "Every actual insertion power", "The antidiagonal expansion sums over ell+k=j with coefficient choose(j,ell)*(r)_ell and state A_i(ell-r)L1^k b. Both inverse-Gram equations are explicit; the ell=r zero-current term survives."),
            Entry("one_pow_current_insertion_bounded", "The exact finite insertion range", "The natural insertion sum runs through ell<=min(j,r), with the original neutral current and actual L1^(j-ell)b."),
            Entry("one_pow_grade", "Signed conformal weight of descendants", "If a has actual integer grade h then L1^j a has grade h-j, including negative weights. Both inverse equations are required."),
            Entry("reversedFirstTerm", "First reversed pointwise term", "The term is choose(t+r-1,r-1) O_b(n+t) A_i(t+r)v.", DescribeRole.Definition),
            Entry("reversedSecondTerm", "Second reversed pointwise term", "The term is choose(s+r-1,r-1) A_i(-s) O_b(n-s-r)v, including s=0.", DescribeRole.Definition),
            Entry("reversed_first_finite", "Finite first reversed support", "Actual current truncation on the tested vector bounds the first reversed support before opposite-mode evaluation."),
            Entry("oppositeInputBound", "A common finite descendant truncation bound", "A finite maximum over the actual Y(L1^j b) thresholds gives one bound on the tested vector for the second reversed order.", DescribeRole.Definition),
            Entry("opposite_reversed_input_zero", "Uniform high reflected-input annihilation", "Above the common descendant bound, every actual Y coefficient in O_b(n-s-r)v vanishes in its original order."),
            Entry("reversed_second_finite", "Finite second reversed support", "The finite maximum over actual descendant truncation thresholds bounds the complete second reversed family; no state-independent occupation cutoff is imposed."))));
}
