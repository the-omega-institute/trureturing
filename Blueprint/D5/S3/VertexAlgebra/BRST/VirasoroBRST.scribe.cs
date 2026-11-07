using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.BRST;

internal sealed class VirasoroBRSTDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Node(string name, string prose) => Describe.Lean(
        DescribeId.Create("virasoro-brst-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/BRST/VirasoroBRST." + name),
        H(name.Replace("_", " ")), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed original bc BRST anomaly for lower-truncated Virasoro matter",
        H("General Virasoro matter and the original bc BRST charge"), Blocks(
            Paragraph(Text("MatterDatum has exactly the original mode family, central charge, integer Virasoro commutator and statewise positive-mode truncation. V is any complex module and State V is exactly V tensor the original countable bc occupation Fock space. No Ward identity, covariance, degree, square, support, positivity or vacuum conclusion is assumed. The charge Q is T plus the identity tensor the native ghost cubic Qg; N is the native ghost number.")),
            Paragraph(Text("T sums matterMode m times c(-m) only after evaluation on a state. Genuine matter lower truncation and the native ghost occupation radius give finite support. Translated paired finite sums have coefficients k-2r and 2r-k; the original Virasoro central singleton at -r survives their cancellation. The finite pure-c Ward operator R commutes with T using a common capture of x and R x. The remaining square residual has degree two and commutes with all original b and c modes, so the charged tensor commutant annihilates it.")),
            Paragraph(Text("The twenty public theorem source-family audits remain unfinished; see https://github.com/the-omega-institute/trureturing/issues/25671 for the exact targets and native statement identities. Empty registration inventory and empty error arrays do not validate an audit. The missing evidence is a lawful enrolled readout and exact polymorphic realization bridge, with actual-positive law, whole-family variation, fixed-other sensitivity and observational dependence proofs.")),
            Node("summand_finite", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, summand_finite (x : State V) : Function.HasFiniteSupport (fun m : \u2124 => summand A m x)."),
            Node("T_apply", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, T_apply (x : State V) : T A x = \u2211\u1da0 m : \u2124, (matterMode A m * ghostC A (-m)) x."),
            Node("finite_capture", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, finite_capture (x : State V) (s : Finset \u2124) (hs : Function.support (fun m : \u2124 => summand A m x) \u2286 (s : Set \u2124)) : T A x = \u2211 m \u2208 s, summand A m x."),
            Node("common_capture", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, common_capture (X : Finset (State V)) : \u2203 s : Finset \u2124, \u2200 x \u2208 X, Function.support (fun m : \u2124 => summand A m x) \u2286 (s : Set \u2124)."),
            Node("number_T", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, number_T : number (V := V) * T A - T A * number (V := V) = T A."),
            Node("ward_b", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, ward_b (r : \u2124) : T A * ghostB A r + ghostB A r * T A = matterMode A r."),
            Node("ward_c", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, ward_c (r : \u2124) : T A * ghostC A r + ghostC A r * T A = 0."),
            Node("matter_covariance_apply", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, matter_covariance_apply (r : \u2124) (x : State V) : (T A * matterMode A r - matterMode A r * T A) x = (\u2211\u1da0 k : \u2124, ((k-2*r : \u2124) : \u2102) \u2022 paired A r k x) + (-((A.centralCharge / 12) * ((r : \u2102)^3-r))) \u2022 ghostC A r x."),
            Node("ghost_covariance_apply", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, ghost_covariance_apply (r : \u2124) (x : State V) : (T A * ghostVirasoro A r - ghostVirasoro A r * T A) x = \u2211\u1da0 k : \u2124, ((2*r-k : \u2124) : \u2102) \u2022 paired A r k x."),
            Node("covariance", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, covariance (r : \u2124) : T A * (matterMode A r + ghostVirasoro A r) - (matterMode A r + ghostVirasoro A r) * T A = (-((A.centralCharge / 12) * ((r : \u2102)^3-r))) \u2022 ghostC A r."),
            Node("Q_ward_b", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, Q_ward_b (r : \u2124) : Q A * ghostB A r + ghostB A r * Q A = Ltotal A r."),
            Node("Q_ward_c", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, Q_ward_c (r : \u2124) : Q A * ghostC A r + ghostC A r * Q A = ghostR A r."),
            Node("Q_R", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, Q_R (r : \u2124) : Q A * ghostR A r - ghostR A r * Q A = 0."),
            Node("Q_Ltotal", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, Q_Ltotal (r : \u2124) : Q A * Ltotal A r - Ltotal A r * Q A = (((26-A.centralCharge) / 12) * ((r : \u2102)^3-r)) \u2022 ghostC A r."),
            Node("N_Q", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, N_Q : N A * Q A - Q A * N A = Q A."),
            Node("residual_b", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, residual_b (r : \u2124) : residual A * ghostB A r = ghostB A r * residual A."),
            Node("residual_c", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, residual_c (r : \u2124) : residual A * ghostC A r = ghostC A r * residual A."),
            Node("square_anomaly", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, square_anomaly : Q A ^ 2 = ((26-A.centralCharge) / 26) \u2022 ghostSquareAnomaly A."),
            Node("square_finite", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, square_finite (x : State V) : Function.HasFiniteSupport (fun n : \u2124 => (((A.centralCharge-26) / 24) * ((n : \u2102)^3-n)) \u2022 ((ghostC A (-n) * ghostC A n) x))."),
            Node("square_apply", "For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, square_apply (x : State V) : (Q A ^ 2) x = \u2211\u1da0 n : \u2124, (((A.centralCharge-26) / 24) * ((n : \u2102)^3-n)) \u2022 ((ghostC A (-n) * ghostC A n) x)."),
            Paragraph(Text("The operator formula scales the native ghost square by (26-centralCharge)/26. Its pointwise form retains all signed integer n and the coefficient (centralCharge-26)/24 times (n cubed minus n) multiplying c(-n)c(n). An anonymous transient check instantiates arbitrary lattice rank using both inverse-Gram identities and the accepted Hahn-order truncation, identifies the actual original lattice T and Q, and applies this general square formula. Critical central charge 26 is checked transiently and introduces no retained specialization. This is algebraic BRST mathematics; it does not complete Monster moonshine, construct BRST cohomology or establish a physical VOA/CFT, string model or AdS/CFT correspondence.")))));
}
