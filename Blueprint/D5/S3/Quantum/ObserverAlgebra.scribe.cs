using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class ObserverAlgebraDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Schwinger =
        LibraryNoteRef.Create("D5/L/schwinger1960unitary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Quantum/ObserverAlgebra",
            "Finite-register read and reversible-update operators form a covariant noncommutative skeleton."),
        H("Finite Observer Read-Update Skeleton"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("specified-permutation-updates-form-a-covariant-group-action"),
                H("Specified permutation updates form a covariant group action"),
                LeanTheorem(
                    "D5/S3/Quantum/ObserverAlgebra.observer_update_covariant_group_skeleton"),
                LatexStatement.Create(@"$$\forall I,\ \forall \tau,\sigma \in \operatorname{Perm}(I),\ \forall f:I\to\mathbb{C},\ \forall \psi:I\to\mathbb{C},\ U_{\operatorname{id}}\psi=\psi \land U_{\sigma\circ\tau}\psi=U_{\sigma}(U_{\tau}\psi) \land U_{\tau^{-1}}(U_{\tau}\psi)=\psi \land U_{\tau}(R_{f}\psi)=R_{f\circ\tau^{-1}}(U_{\tau}\psi)$$"),
                DescribeProvenance.LiteratureAttested(Schwinger),
                Blocks(Paragraph(Text(
                    "The register index type may be arbitrary, including an empty type. Explicitly supplied permutations act by pullback on complex amplitude functions; identity, composition, inverse, and covariance with pointwise multiplication reads are proved together. This is a represented finite-register skeleton. It does not construct or identify the universal C*-crossed product, prove its universal property, exclude continuous hidden flows, derive discreteness or an integer action, or force quantum structure from a classical ontology. Original numerical-certificate disposition: neither observer-algebra CAS atom contains a numerical certificate.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("changed-read-values-witness-noncommutativity"),
                H("Changed read values witness noncommutativity"),
                LeanTheorem(
                    "D5/S3/Quantum/ObserverAlgebra.observer_read_update_noncommutative"),
                LatexStatement.Create(@"$$\forall I,\ \forall \tau \in \operatorname{Perm}(I),\ \forall f,\psi:I\to\mathbb{C},\ \forall i\in I,\ f(\tau^{-1}i)\neq f(i) \land \psi(\tau^{-1}i)\neq 0 \Rightarrow U_{\tau}(R_{f}\psi)\neq R_{f}(U_{\tau}\psi)$$"),
                DescribeProvenance.LiteratureAttested(Schwinger),
                Blocks(Paragraph(Text(
                    "Noncommutativity requires an explicit address i where the pulled-back read value differs from the current read value and a state whose predecessor amplitude is nonzero. That address is also the explicit inhabitability witness; there is no hidden Nonempty premise. The theorem does not say that every read function, reversible update, or state fails to commute, and it does not assert an abstract C*-algebra commutator identity. Original numerical-certificate disposition: neither observer-algebra CAS atom contains a numerical certificate.")))
            ))));
}
