using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;
internal sealed class AffineCodebookMemoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual affine codebooks retain hidden memory and have a sharp autonomous readout.",
        H("Affine Codebook Memory"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-on-actual-span"),
                DeclarationHandle.Create("D5/S3/Observer/LinearMemory/AffineCodebookMemory.fixed_on_actual_span"),
                H("Affine fixedness fixes the centered span"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The arithmetic mean is affine fixed. Differences from that mean lie in the kernel of A minus identity. Nonconstancy forces the actual centered span U to be nonzero. Repetitions in the finite codebook are allowed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-projection-and-blocks"),
                DeclarationHandle.Create("D5/S3/Observer/LinearMemory/AffineCodebookMemory.actual_projection_and_blocks"),
                H("The actual orthogonal decomposition and typed blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("P is orthogonal projection onto the centered span, Q is one minus P, and W is its orthogonal complement. The proof identifies Q with the orthogonal projection onto W and B,D with FourBlockDecomposition hiddenVisibleInfluence and residualInternalBlock, including their domain projection normalization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-error-and-recursions"),
                DeclarationHandle.Create("D5/S3/Observer/LinearMemory/AffineCodebookMemory.actual_error_and_recursions"),
                H("Every actual driven trajectory has both projected recurrences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary state-dependent forcing, centering at any fixed codepoint gives the full error recurrence and the visible and hidden block recurrences. No independence, zero mean, nonzero hidden space, or invertibility is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("driven-finite-solution"),
                DeclarationHandle.Create("D5/S3/Observer/LinearMemory/AffineCodebookMemory.driven_finite_solution"),
                H("The arbitrary driven finite-time solution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real module, endomorphism L, forcing f and sequence satisfying x(t+1)=L(x(t))+f(t), every n has x(n)=L^n x(0)+sum over j<n of L^(n-1-j)f(j). The zero-time sum is empty. Applying this to the actual D and hidden forcing gives the entire finite convolution and the visible memory kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-inverse-data"),
                DeclarationHandle.Create("D5/S3/Observer/LinearMemory/AffineCodebookMemory.actual_inverse_data"),
                H("The actual contractive inverse and its finite remainder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under norm(D)<=q<1, H is Ring.inverse(1-D), not an assumed inverse. The proof directly uses the pinned Neumann-series suppliers to obtain both inverse products, the infinite series, and every finite inverse remainder. Finite-dimensional completeness is explicit and W=0 is retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-power-bound"),
                DeclarationHandle.Create("D5/S3/Observer/LinearMemory/AffineCodebookMemory.actual_power_bound"),
                H("A power bound that includes the zero hidden space"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pointwise operator estimate bounds norm(D^n) by q^n without assuming norm(identity)=1 on a possibly zero vector space. This consumed helper supports the finite geometric bound and bounded hidden trajectories."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-power-bound"),
                DeclarationHandle.Create("D5/S3/Observer/LinearMemory/AffineCodebookMemory.finite_power_bound"),
                H("The uniform finite geometric bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite sum of powers of the same actual D has operator norm at most 1/(1-q). The denominator is positive because the given norm bound implies q>=0 and q<1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-constant-hidden-drift"),
                DeclarationHandle.Create("D5/S3/Observer/LinearMemory/AffineCodebookMemory.actual_constant_hidden_drift"),
                H("Contractive hidden error and visible linear drift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For r(t)=0 and s(t)=w, the same inverse H and K=BH give v(t)=Hw+D^t(v(0)-Hw) and u(n)-u(0)=n Kw+B(sum over t<n of D^t)(v(0)-Hw). The remainder norm is at most norm(B)/(1-q) times norm(v(0)-Hw), the normalized visible error tends to Kw, and the hidden sequence is bounded. All w have K w=0 iff B=0, including B=0, W=0, q=0 and n=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orthogonal-row-norm"),
                DeclarationHandle.Create("D5/S3/Observer/LinearMemory/AffineCodebookMemory.orthogonal_row_norm"),
                H("The sharp Euclidean row norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonzero U and any continuous linear K:W to U, the orthogonal Euclidean row p_U+K p_W has norm sqrt(1+norm(K)^2). The proof identifies the actual adjoint column, uses Pythagoras, and establishes matching upper and lower operator bounds. It includes W=0 and uses the Euclidean sum norm."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-autonomous-readout"),
                DeclarationHandle.Create("D5/S3/Observer/LinearMemory/AffineCodebookMemory.actual_autonomous_readout"),
                H("The unique autonomous readout and its stable graph"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the same actual contraction, PiStar=p_U+K p_W restricts to identity on U and satisfies PiStar A=PiStar. Uniqueness ranges over all linear readouts, without a continuity hypothesis. Its kernel is exactly the graph (-K v,v), that graph is A-invariant and every iterate on it tends to zero. The readout preserves every codepoint difference, has the sharp norm, and every driven recurrence satisfies z(t+1)=z(t)+r(t)+K s(t)."))),
                DescribeRole.Theorem),
            Paragraph(Text("The escape-registration audit for all ten public targets is unfinished and tracked at https://github.com/the-omega-institute/trureturing/issues/18516. This issue supplies neither a registration proof nor declared_validated status; the mathematical statements and existing validation gates retain their full scope.")),
            Paragraph(Text("The complete original section 14 application additionally checks the universal accumulation criterion for every initial error and every forcing: it holds iff B=0 iff the actual projection kernel is A-invariant. A specified trajectory instead needs precisely B v(t)=0 at each simplified step. The chosen-complement equivalence is directly reused from VisibleHiddenProjectionCriteria.")),
            Paragraph(Text("The specified real two-dimensional example has codepoints (-1,0),(1,0), mean zero, actual coordinate-axis projections, A=[[1,1],[0,1/2]], and b=0. Its cross block sends beta e2 to beta e1 and its hidden block sends beta e2 to (beta/2)e2. With initial c_minus+e2 and no forcing, every t has v(t)=2^(-t)e2 and u(t)=2(1-2^(-t))e1; u(0)=0, u(1)=e1, and every direct visible forcing is zero. This establishes conditional insufficiency of ambient projected accumulation under affine neutrality; it makes no wholesale refutation claim about a differently restricted corollary.")),
            Paragraph(Text("For every actual finite injective codebook on a nontrivial state set, the set of distances of distinct pairs is finite and nonempty; its sInf is attained at a distinct pair and strictly positive. With this actual minimum, the full existing SmoothFiniteMachineRealization.smooth_finite_machine_realization is applied unchanged. It provides global C1 maps for arbitrary transitions and outputs, all words and prefixes, every initial closed r-ball, and every bounded post-update perturbation for 0<=nu<r<R<Delta/2, including nu=0. No bump function, decoder or word induction is redeveloped here. These applications are transient Lean evidence and exposition, not new retained supplier wrappers.")),
            Paragraph(Text("The all-constant-drive trajectory statement is checked using the same actual drift theorem and uniqueness of limits: every normalized visible trajectory has zero limit for all hidden drives iff B=0. The autonomous readout transforms hidden forcing into K s(t); it neither removes that drift nor supplies automatic error correction. No neural architecture, training, resource or literature novelty claim is made."))
        )));
}
