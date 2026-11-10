using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NormFourVacuumIrreducibleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual cyclic norm-four lattice Virasoro vacuum representation is irreducible.",
        H("Irreducibility of the Actual Cyclic Vacuum Representation"),
        Blocks(
            Paragraph(Text("Let D have an integral symmetric Gram matrix with even diagonal, let a be a "
                + "charge with B(a,a)=4, and let s in C satisfy s squared equal to one. Write L_m for "
                + "the actual mode Y(v)_(m+1) of the norm-four lattice state v on the finite-support carrier.")),
            Describe.Lean(
                DescribeId.Create("normfourvacuumirreducible-vacuum-descendants"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourVacuumIrreducible.vacuumDescendants"),
                H("The cyclic vacuum space"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D,a,s, vacuumDescendants is the complex linear span of "
                    + "all finite words L_(-(k_1+1)) ... L_(-(k_r+1)) vacuum, with all k_i natural. "
                    + "The empty word is the actual vacuum. These word vectors may vanish or be linearly dependent."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normfourvacuumirreducible-restricted-mode"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourVacuumIrreducible.restrictedMode"),
                H("Every integer mode restricts to the cyclic space"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every such D,a,s and every integer m, restrictedMode is the "
                    + "restriction of the actual L_m to vacuumDescendants. Closure follows by induction "
                    + "on negative words using the actual Virasoro commutator, including its central term, "
                    + "and creativity on the vacuum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normfourvacuumirreducible-vacuum-descendants-irreducible"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourVacuumIrreducible.vacuum_descendants_irreducible"),
                H("The invariant-subspace dichotomy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every such D,a,s and every complex submodule U of "
                    + "vacuumDescendants, if restrictedMode m maps every element of U into U for "
                    + "every integer m, then U is zero or the whole cyclic space. There is no positivity, "
                    + "rootlessness, PBW basis, eigenbasis or grading assumption on U."))),
                DescribeRole.Theorem),
            Paragraph(Text("A negative word has natural grade equal to the sum of its positive indices. "
                + "The actual L_0 acts on it by that grade, and grade zero is exactly the vacuum line. "
                + "Span induction gives a finite homogeneous expansion of every cyclic vector. "
                + "For a finite support S and n in S, the polynomial product of L_0-j over j in S "
                + "different from n kills every other component. Its value on the n component is "
                + "a nonzero scalar, so every L_0-invariant subspace contains each component.")),
            Paragraph(Text("A nonzero invariant subspace therefore has a nonzero vector of least natural "
                + "grade n. Every positive actual mode kills this vector: otherwise the commutator "
                + "would produce a nonzero eigenvector of smaller natural grade. The highest-weight "
                + "restriction gives n equal to 0, 1/16 or 1/2. Since n is natural, it equals zero. "
                + "The subspace contains the vacuum line and hence every negative word, proving cyclic irreducibility.")),
            Paragraph(Text("The norm-four state retains its Dong-Mason-Zhu and Shimakura attribution; "
                + "the lattice construction and residue calculus retain their Bakalov-Kac, Carnahan "
                + "and Matsuo-Nagatomo attribution. This conclusion concerns the cyclic Virasoro "
                + "representation. Bundled VOA simplicity, fusion, anomalies, Monster moonshine "
                + "and string or AdS-CFT realization require further results.")))));
}
