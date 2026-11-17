using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar;
internal sealed class UniformSchmidtHeadCapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A literal APPT spectrum in any local dimensions at least six satisfies a necessary homogeneous bound on its largest eigenvalue. The proof uses an actual independent Bell assignment and compares quadratic forms only on nonnegative vectors.",
        H("UniformSchmidtHeadCap"), Blocks(
            Paragraph(Text("Let l be a nonnegative antitone spectrum of mass one and length m*n, with m,n at least six. Let u be its entry at zero-based index m*n-21, let u+v be its entry at index 14, and let L be its entry at index 0. Literal APPT refers to the diagonal matrix formed with the supplied product-coordinate equivalence.")),
            Paragraph(Text("The existing literal_assignment_psd theorem supplies positive semidefiniteness for every actual independent assignment. Assign L to edge (0,1). Diagonal entries are at most 2u, ordinary off-diagonal entries are at most -v, and the exceptional two entries are at most u-L. Entrywise domination is used only after multiplication by nonnegative vector coordinates; no Loewner-order implication is asserted.")),
            Paragraph(Text("The all-ones test gives 15v <= 6u. Nonnegativity, sortedness, mass one and the actual charge identity give u>0, including spectra with zero eigenvalues. For x=(p,p,q,q,q,q), half the model quadratic form is (3u-L)p^2-8vpq+(4u-6v)q^2. Setting p=2u-3v>0 and q=2v gives the head bound.")),
            Describe.Lean(DescribeId.Create("uniformschmidtheadcap-literal-rank-six-head-cap"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/UniformSchmidtHeadCap.literal_rank_six_head_cap"),
                H("Literal rank-six head cap"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every m,n>=6, product-coordinate equivalence e, antitone nonnegative spectrum l with sum one, and literal APPT of diagonal(l composed with e), the actual u,v,L defined above satisfy u>0, v>=0, 15v<=6u, L-u-v>=0, 8v^2<=(3u-L)(2u-3v), and L-u-v<=2u-v-8v^2/(2u-3v)."))),
                DescribeRole.Theorem),
            Paragraph(Text("Writing h=L-u-v and scaling u to one gives h<=(2-5v)(2+v)/(2-3v). This is a necessary APPT constraint, with ties and singular positive semidefinite assignments included. It supplies no converse, purity optimum, attainment, uniqueness or eventual threshold n0(6). The unrestricted original conjecture is not claimed to be resolved.")),
            Paragraph(Text("Utility none: the only public theorem is a symbolic inequality for every actual normalized spectrum in all ambient local dimensions at least six. Private cardinality, quadratic-form and order helpers are consumed by that theorem. Evaluating a symbolic six-coordinate quadratic form does not provide a standalone bounded-instance certificate."))
        )));
}
