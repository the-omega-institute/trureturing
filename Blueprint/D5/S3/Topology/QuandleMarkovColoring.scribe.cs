using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class QuandleMarkovColoringDocument : IScribeDocumentDefinition
{
    private static AssessedProvenance Source => AssessedProvenance.FromLiterature(
        LibraryNoteRef.Create("D5/L/Topology/fennrourke1992racks"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quandle coloring spaces are preserved by both signed algebraic Markov stabilizations.",
        H("Quandle Colorings of Algebraic Braid Closures"),
        Blocks(
            Describe.Lean(DescribeId.Create("quandle-braid-action-colors"),
                DeclarationHandle.Create("D5/S3/Topology/QuandleMarkovColoring.Colors"),
                H("Boundary colorings"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A boundary coloring is a function from Fin n to an arbitrary rack Q. Neither finiteness nor quandle idempotence is assumed. At zero strands the coloring space consists of the unique empty function, including when Q itself is empty."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quandle-braid-action-representation"),
                DeclarationHandle.Create("D5/S3/Topology/QuandleMarkovColoring.braidAction"),
                H("Artin action on rack colors"), StatementSource.WithoutFormula(), Source,
                Blocks(
                    Paragraph(Text("The local crossing sends (x,y) to (x ◃ y,x); its inverse sends (x,y) to (y,y ◃⁻¹ x). In an n-strand coloring these maps update only two adjacent coordinates. The existing local inverse and Yang–Baxter theorems supply the pair and three-coordinate identities. Disjoint coordinate updates commute, so the distant and adjacent Artin relators act trivially.")),
                    Paragraph(Text("The resulting group homomorphism is defined on the existing literal n-strand Artin presentation, with values in permutations of the entire coloring space. It applies to infinite and empty racks as well as finite racks, and includes zero and one strands, which have no crossing generators. Multiplication applies the right factor first. No geometric braid identification or knot-closure theorem is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quandle-braid-action-last-slot"),
                DeclarationHandle.Create("D5/S3/Topology/QuandleMarkovColoring.lastSlot"),
                H("Final old coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a strictly positive strand count n, the final old coordinate is the element n−1 of Fin n. The positivity hypothesis supplies a genuine coordinate for the stabilization formulas."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quandle-markov-closed-colorings"),
                DeclarationHandle.Create("D5/S3/Topology/QuandleMarkovColoring.ClosedColorings"),
                H("Closed boundary colorings"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a rack Q and an element of the literal n-strand Artin group, a closed coloring is a function from Fin n to Q fixed by its braid transport."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quandle-markov-positive-equivalence"),
                DeclarationHandle.Create("D5/S3/Topology/QuandleMarkovColoring.positiveStabilizationEquiv"),
                H("Positive stabilization"), StatementSource.WithoutFormula(), Source,
                Blocks(Paragraph(Text("For every quandle, every strictly positive strand count and every braid, positive stabilization preserves the entire coloring space. The forward map appends the old last color and the inverse restricts to the original coordinates. Comparing the last coordinate forces the appended color; idempotence removes the remaining crossing. The quandle may be infinite or empty."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quandle-markov-negative-equivalence"),
                DeclarationHandle.Create("D5/S3/Topology/QuandleMarkovColoring.negativeStabilizationEquiv"),
                H("Negative stabilization"), StatementSource.WithoutFormula(), Source,
                Blocks(Paragraph(Text("Negative stabilization has the same diagonal extension and restriction maps. Its last coordinate equation uses the inverse rack action. Injectivity of that action and quandle idempotence force the added color to equal the old last color. Both inverse laws hold without a finiteness assumption."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quandle-markov-conjugation-equivalence"),
                DeclarationHandle.Create("D5/S3/Topology/QuandleMarkovColoring.conjugationEquiv"),
                H("Conjugation of closed braids"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transport by a conjugating braid identifies the fixed-coloring spaces of a braid and its conjugate. The inverse uses transport by the inverse conjugating braid."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quandle-markov-coloring-count"),
                DeclarationHandle.Create("D5/S3/Topology/QuandleMarkovColoring.coloringCount"),
                H("Coloring count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The count is the natural cardinality of the closed-coloring type. It is an ordinary finite count when the color quandle is finite."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quandle-markov-invariance"),
                DeclarationHandle.Create("D5/S3/Topology/QuandleMarkovColoring.quandle_coloring_markov_invariant"),
                H("Algebraic Markov invariance"), StatementSource.WithoutFormula(), Source,
                Blocks(
                    Paragraph(Text("For every finite quandle, any two positive-strand braids connected by a finite equivalence chain of conjugations and either signed Markov stabilization have equal coloring counts. The chain uses the existing Artin presentation, strand inclusion and signed last generators; products act by applying the right factor first.")),
                    Paragraph(Text("The quandle assumption cannot in general be replaced by a rack assumption: on two colors, the constant-action rack whose every left translation swaps the colors has two colorings of the one-strand identity and no fixed colorings after either signed stabilization. Zero strands are excluded because there is no final old coordinate.")),
                    Paragraph(Text("This is the classical algebraic coloring construction. A geometric identification of the algebraic Markov quotient with link closures is an additional theorem. The result asserts no such identification, classification of knots or new topological invariant."))),
                DescribeRole.Theorem))));
}
