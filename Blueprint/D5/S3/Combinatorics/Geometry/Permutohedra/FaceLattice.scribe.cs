using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry.Permutohedra;

internal sealed class FaceLatticeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/rossi2026permutohedron");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The permutohedron face lattice.",
        H("The permutohedron face lattice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("facelattice-cutchain"),
                DeclarationHandle.Create(Module + ".CutChain"),
                H("Cut chains"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A cut chain on n labels is a finite set of subsets of Fin n. Each cut has cardinality strictly between zero and n, and every two cuts are comparable by inclusion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("facelattice-cutchain-ext-cuts"),
                DeclarationHandle.Create(Module + ".ext_cuts"),
                H("Equality of cut chains"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Two cut chains on the same labels are equal if their sets of cuts are equal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("facelattice-face"),
                DeclarationHandle.Create(Module + ".Face"),
                H("Faces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Face n is the type obtained by adjoining a bottom element to the cut chains on Fin n. The order on chains is reverse inclusion of their cut sets."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("facelattice-facesup"),
                DeclarationHandle.Create(Module + ".faceSup"),
                H("Binary join operation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Intersect the cut sets of two chains. If either input is bottom, return the other input."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("facelattice-facesup-lub"),
                DeclarationHandle.Create(Module + ".faceSup_lub"),
                H("Join"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For any two faces, their binary join is the least upper bound of the pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("facelattice-compatible"),
                DeclarationHandle.Create(Module + ".compatible"),
                H("Compatible cut chains"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Two cut chains are compatible if every two cuts in the union of their cut sets are comparable by inclusion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("facelattice-faceinf"),
                DeclarationHandle.Create(Module + ".faceInf"),
                H("Binary meet operation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take the union of the cuts of two compatible chains. Return bottom if either input is bottom or the chains are incompatible."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("facelattice-faceinf-glb"),
                DeclarationHandle.Create(Module + ".faceInf_glb"),
                H("Meet"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For any two faces, their binary meet is the greatest lower bound of the pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("facelattice-flag"),
                DeclarationHandle.Create(Module + ".flag"),
                H("Permutation flags"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The flag of a permutation of Fin n is the cut chain consisting of its unordered prefixes at all ranks strictly between zero and n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("facelattice-cutchain-eq-of-card-eq"),
                DeclarationHandle.Create(Module + ".eq_of_card_eq"),
                H("A cut is determined by its size within a chain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Two cuts belonging to the same chain are equal if their cardinalities agree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("facelattice-mem-flag"),
                DeclarationHandle.Create(Module + ".mem_flag"),
                H("Flag membership at a cut's rank"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A subset with cardinality strictly between zero and n belongs to a permutation flag exactly when the prefix of that cardinality equals the subset."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("facelattice-prefix-mem-flag"),
                DeclarationHandle.Create(Module + ".prefix_mem_flag"),
                H("Proper prefixes belong to their flags"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At every rank strictly between zero and n, the prefix of a permutation is a cut of its flag."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("facelattice-atom"),
                DeclarationHandle.Create(Module + ".atom"),
                H("The face of a permutation flag"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("View the flag of a permutation as a face via the inclusion of cut chains into Face n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("facelattice-atom-isatom"),
                DeclarationHandle.Create(Module + ".atom_isAtom"),
                H("Permutation faces are atoms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The face of each permutation flag is an atom. Any chain below it would contain the flag and can add no cut, since the flag already has a cut at every proper rank."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("facelattice-rank"),
                DeclarationHandle.Create(Module + ".rank"),
                H("Face rank"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The integer rank is minus one at bottom and n minus one minus the number of cuts at a chain on n labels."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("facelattice-join-eq"),
                DeclarationHandle.Create(Module + ".join_eq"),
                H("Recognizing a finite join"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Suppose a finite family contains a face above bottom. If a chain contains precisely the cuts shared by every chain in the family, then that chain is the finite join of the family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("facelattice-sup-cuts"),
                DeclarationHandle.Create(Module + ".sup_cuts"),
                H("Finite joins"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("When a finite join is a cut chain, a cut belongs to that chain exactly when it belongs to every member that lies above bottom. The empty join is bottom, whose rank is minus one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("facelattice-strict-of-extra-cut"),
                DeclarationHandle.Create(Module + ".strict_of_extra_cut"),
                H("An extra common cut forces strict inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Suppose the join of a finite family is at most a chain x. If some cut is absent from x and belongs to every chain in the family, the join lies strictly below x."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("facelattice-proper-lt-of-erase-lt"),
                DeclarationHandle.Create(Module + ".proper_lt_of_erase_lt"),
                H("Strict inequality for proper subfamilies"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("In a join-semilattice with bottom and decidable equality, let A be a finite set. If deleting any one member of A gives a join strictly below x, every proper subset of A has join strictly below x."))),
                DescribeRole.Theorem))));
}
