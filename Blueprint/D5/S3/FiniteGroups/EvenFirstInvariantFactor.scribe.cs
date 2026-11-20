using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class EvenFirstInvariantFactorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/EvenFirstInvariantFactor.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/mazhang2026bajnokbeatty");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An s-spanning pair of Z/c × Z/(ck) with c even forces c²k ≤ 2s², with equality only "
            + "when c divides s.",
        H("The even first invariant factor"),
        Blocks(
            Describe.Lean(DescribeId.Create("even-first-invariant-factor"),
                DeclarationHandle.Create(Prefix + "even_factor"),
                H("Spanning pairs with an even first invariant factor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Let c ≥ 2 be even, k, s ≥ 1, and let a, b be elements of "
                    + "G = Z/c × Z/(ck) such that every element of G is xa + yb with integers "
                    + "|x| + |y| ≤ s. Then |G| = c²k ≤ 2s². If equality holds then c divides s, "
                    + "and if s is odd then c²k ≤ 2s² − 2. The relation lattice K of the pair "
                    + "lies in cZ², hence in 2Z². Pulling it back along T(u,v) = (u+v, u−v) gives "
                    + "a lattice M of index |G|/2. Because every relation is even, a Lee "
                    + "representative of length at most s of the right parity class yields a "
                    + "representative of each coset of M in the square [0,s)², so |G|/2 ≤ s². At "
                    + "equality the near-square rigidity of a lattice of index s² covered by that "
                    + "square gives a basis putting (s,s) or (s,−s) into K, so c divides s; for odd "
                    + "s this is impossible, and 4 | |G| sharpens the bound by 2. This is "
                    + "Corollary 8 of H. Ma and W. Zhang on the Bajnok–Beatty conjectures; it "
                    + "allows any spanning pair, where Bajnok and Beatty's even-c results assume "
                    + "the special form {(1,u),(1,v)}."))),
                DescribeRole.Theorem))));
}
