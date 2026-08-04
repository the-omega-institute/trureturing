using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

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
                LeanTheorem("D5/S3/Quantum/ObserverAlgebra.observer_update_covariant_group_skeleton"),
                Disp(Seq(Forall, Sp, F.Id("I"), Comma, Esc, Forall, Sp, Tau, Comma, SigmaLower, Sp, InMacro, Sp, Operatorname, Grp(F.Id("Perm")), Open, F.Id("I"), Close, Comma, Esc, Forall, Sp, F.Id("f"), Colon, F.Id("I"), To, Mathbb, Grp(F.Id("C")), Comma, Esc, Forall, Sp, Psi, Colon, F.Id("I"), To, Mathbb, Grp(F.Id("C")), Comma, Esc, F.Id("U"), Underscore, Grp(Operatorname, Grp(F.Id("id"))), Psi, Eq, Psi, Sp, Land, Sp, F.Id("U"), Underscore, Grp(SigmaLower, Circ, Tau), Psi, Eq, F.Id("U"), Underscore, Grp(SigmaLower), Open, F.Id("U"), Underscore, Grp(Tau), Psi, Close, Sp, Land, Sp, F.Id("U"), Underscore, Grp(Tau, Caret, Grp(Minus, D(1))), Open, F.Id("U"), Underscore, Grp(Tau), Psi, Close, Eq, Psi, Sp, Land, Sp, F.Id("U"), Underscore, Grp(Tau), Open, F.Id("R"), Underscore, Grp(F.Id("f")), Psi, Close, Eq, F.Id("R"), Underscore, Grp(F.Id("f"), Circ, Tau, Caret, Grp(Minus, D(1))), Open, F.Id("U"), Underscore, Grp(Tau), Psi, Close)),
                DescribeProvenance.LiteratureAttested(Schwinger),
                Blocks(Paragraph(Text(
                    "The register index type may be arbitrary, including an empty type. Explicitly supplied permutations act by pullback on complex amplitude functions; identity, composition, inverse, and covariance with pointwise multiplication reads are proved together. This is a represented finite-register skeleton. It does not construct or identify the universal C*-crossed product, prove its universal property, exclude continuous hidden flows, derive discreteness or an integer action, or force quantum structure from a classical ontology. Original numerical-certificate disposition: neither observer-algebra CAS atom contains a numerical certificate.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("changed-read-values-witness-noncommutativity"),
                H("Changed read values witness noncommutativity"),
                LeanTheorem("D5/S3/Quantum/ObserverAlgebra.observer_read_update_noncommutative"),
                Disp(Seq(Forall, Sp, F.Id("I"), Comma, Esc, Forall, Sp, Tau, Sp, InMacro, Sp, Operatorname, Grp(F.Id("Perm")), Open, F.Id("I"), Close, Comma, Esc, Forall, Sp, F.Id("f"), Comma, Psi, Colon, F.Id("I"), To, Mathbb, Grp(F.Id("C")), Comma, Esc, Forall, Sp, F.Id("i"), InMacro, Sp, F.Id("I"), Comma, Esc, F.Id("f"), Open, Tau, Caret, Grp(Minus, D(1)), F.Id("i"), Close, Neq, Sp, F.Id("f"), Open, F.Id("i"), Close, Sp, Land, Sp, Psi, Open, Tau, Caret, Grp(Minus, D(1)), F.Id("i"), Close, Neq, Sp, D(0), Sp, Rightarrow, Sp, F.Id("U"), Underscore, Grp(Tau), Open, F.Id("R"), Underscore, Grp(F.Id("f")), Psi, Close, Neq, Sp, F.Id("R"), Underscore, Grp(F.Id("f")), Open, F.Id("U"), Underscore, Grp(Tau), Psi, Close)),
                DescribeProvenance.LiteratureAttested(Schwinger),
                Blocks(Paragraph(Text(
                    "Noncommutativity requires an explicit address i where the pulled-back read value differs from the current read value and a state whose predecessor amplitude is nonzero. That address is also the explicit inhabitability witness; there is no hidden Nonempty premise. The theorem does not say that every read function, reversible update, or state fails to commute, and it does not assert an abstract C*-algebra commutator identity. Original numerical-certificate disposition: neither observer-algebra CAS atom contains a numerical certificate.")))
            ))));
}
