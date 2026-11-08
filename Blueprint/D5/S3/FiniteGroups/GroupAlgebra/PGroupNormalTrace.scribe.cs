using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class PGroupNormalTraceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Webb =
        LibraryNoteRef.Create("D5/L/FiniteGroups/webb2016pgroups");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The modular group algebra links a Galois orbit to its field trace.",
        H("Trace Detects Normal Elements for Galois p-Groups"),
        Blocks(Describe.Lean(
            DescribeId.Create("p-group-normal-element-trace"),
            DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/PGroupNormalTrace.linearIndependent_conjugates_iff_trace_ne_zero"),
            H("Independent conjugates exactly when trace is nonzero"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Webb),
            Blocks(
                Paragraph(Text("For every finite Galois extension L/K in characteristic p whose full Galois group is a p-group, and every x in L, the family of all conjugates of x is K-linearly independent if and only if its field trace is nonzero. Since the Galois group has cardinality equal to the extension degree, this also says that the conjugates form a basis. The group need not be cyclic or abelian, and K need not be finite.")),
                Paragraph(Text("Use Mathlib's normal basis to identify K[G] linearly with L. In these coordinates, group multiplication agrees with the Galois action and trace is augmentation multiplied by the trace of the chosen normal element. Nonzero trace forces nonzero augmentation. The structural cardinal nilpotence theorem proves every element of the augmentation kernel nilpotent. The consumed Apache-2.0 unit criterion from Kitamura's AllPrimeGroups then makes the coordinate element a unit; right multiplication by it preserves independence. Conversely, a zero trace would give the nonzero all-ones linear relation between independent conjugates.")),
                Paragraph(Text("The unit criterion is reused from immutable revision 9253775c275153b1efb04f911b5c8740fed5a568 of KitaKen1/all-prime-residually-finite-p-groups, AllPrimeGroups/NilAugmentation.lean. Its source toolchain v4.34.1 differs from this repository's pin, so the consumed theorem is transplanted with its license and NOTICE. Its nilpotence hypothesis is discharged by the structural cardinal bound."))),
            DescribeRole.Theorem))));
}
