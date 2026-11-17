using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FourPathRadialBoundaryDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Definition(string id, string selector, string title, string text) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathRadialBoundary." + selector),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact ambient geometry of the literal four-path inequality domain and its explicit positive homogeneous radial functional.",
        H("Four-path radial boundary"),
        Blocks(
            Definition("four-path-radial-point", "Point", "Ambient space",
                "Point is the complex coordinate space Fin 4 to Complex, with its ambient product topology and real scalar multiplication."),
            Definition("four-path-radial-min", "minMod", "Minimum modulus",
                "minMod(w) is min(min(|w0|,|w1|),min(|w2|,|w3|)). Repeated minima are retained without selecting an index."),
            Definition("four-path-radial-max", "maxMod", "Maximum modulus",
                "maxMod(w) is max(max(|w0|,|w1|),max(|w2|,|w3|)). Repeated maxima are retained without selecting an index."),
            Definition("four-path-radial-total", "totalMod", "Total modulus",
                "totalMod(w) is |w0|+|w1|+|w2|+|w3|."),
            Definition("four-path-radial-domain", "W", "Literal inequality domain",
                "W is defined independently by all four inequalities |wj| <= 1 and totalMod(w)-2 minMod(w) <= 2. It is not defined as a sublevel set of m."),
            Definition("four-path-radial-functional", "m", "Explicit radial functional",
                "m(w) is max(maxMod(w),(totalMod(w)-2 minMod(w))/2). No triangle inequality, norm law or convexity is part of the definition."),
            Describe.Lean(
                DescribeId.Create("four-path-exact-radial-boundary"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathRadialBoundary.exact_radial_boundary"),
                H("Complete radial geometry"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The weak sublevel {w : m(w) <= 1} equals W. Its ambient interior is {w : m(w) < 1}, and its ambient frontier is {w : m(w) = 1}. Equivalently the frontier consists of points in W satisfying maxMod(w)=1 or totalMod(w)-2 minMod(w)=2. The disjunction is inclusive: tied extrema and simultaneous saturation are preserved.")),
                    Paragraph(Text("For every nonzero w in W there exist t and z with 0<t<=1, t=m(w), m(z)=1 and w=t z. For every real s>0 and every y with m(y)=1 and w=s y, the theorem proves both s=t and y=z; the competing representation need not be supplied with s<=1. The proof divides by m(w) only after proving positivity from w nonzero. Zero remains in W and its interior, and no radial division is performed there.")),
                    Paragraph(Text("Continuity and positive homogeneity follow from the displayed finite modulus formula. At every z with m(z)=1 the proof constructs u(n)=(1+1/(n+1))z. These points converge to z and all lie outside W, since m(u(n))=1+1/(n+1)>1. This construction excludes such z from the interior and supplies the reverse boundary inclusion; it does not assume that inclusion.")),
                    Paragraph(Text("This is the literal geometric content of Definition 23.1, Definition 27.1 and Lemma 27.2 of the four-path recovery theory. It does not identify W with diagonals of actual unitary matrices, establish a producer realization or comparison, or prove the full recovery endpoint. Those require their separate bridges. The finite minimum and maximum formulas include all zero coordinates, boundary parameter t=1, and overlaps of the two saturation types."))),
                DescribeRole.Theorem))));
}
