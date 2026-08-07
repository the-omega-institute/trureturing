using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class RobertsonSchrodingerDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Robertson =
        LibraryNoteRef.Create("D5/L/Quantum/robertson1929uncertainty");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/QuantumBounds/RobertsonSchrodinger",
            "Centered vectors satisfy an exact Robertson-Schrodinger identity with a nonnegative Gram remainder."),
        H("Robertson-Schrodinger Identity"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("centered-vectors-satisfy-the-robertson-schrodinger-identity"),
                H("Centered vectors satisfy the Robertson-Schrodinger identity"),
                LeanTheorem(
                    "D5/S3/QuantumBounds/RobertsonSchrodinger.robertson_schrodinger"),
                RobertsonSchrodingerFormula(),
                DescribeProvenance.LiteratureAttested(Robertson),
                Blocks(
                    Paragraph(Text(
                        "The parent declaration `gram_wedge_identity` applies to arbitrary vectors "
                        + "u and v in any normed additive commutative group with a complex "
                        + "inner-product-space structure. It defines G as the product of the squared "
                        + "norms minus the squared norm of the inner product, states the defining "
                        + "equality, and proves G nonnegative from mathlib's Cauchy-Schwarz theorem. "
                        + "It assumes no operators, symmetricity, distinguished vector, or "
                        + "normalization.")),
                    Paragraph(Text(
                        "The adapter takes complex-linear symmetric operators A and B and a unit "
                        + "vector psi. Its centered vectors u and v have squared norms equal to the "
                        + "two variances. The real part of their inner product is the symmetric "
                        + "covariance Cov, while the complex coercion of the imaginary part is one "
                        + "over two i times the expectation of AB minus BA. Substitution into the "
                        + "parent identity gives the displayed equality with the same nonnegative G.")),
                    Paragraph(Text(
                        "Robertson's 1929 relation retains the commutator lower bound, and "
                        + "Schrodinger's 1930 refinement additionally retains the symmetric "
                        + "covariance term. The exact equality here also retains the Gram remainder: "
                        + "discarding G recovers the strengthened lower bound, and discarding both "
                        + "G and the covariance contribution recovers the weaker bound. No "
                        + "finite-dimensional, completeness, spectral, or unbounded-operator domain "
                        + "theory is asserted.")))
            ))));

    private static Formula RobertsonSchrodingerFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")), Sp,
        Forall, Sp, F.Id("E"), Colon, Sp,
        Operatorname, Grp(F.Id("Type")), Caret, Grp(Star), Comma, Esc,
        OpenBracket, Operatorname, Grp(F.Id("NormedAddCommGroup")),
        Open, F.Id("E"), Close, CloseBracket, Comma, Esc,
        OpenBracket, Operatorname, Grp(F.Id("InnerProductSpace")),
        Open, Mathbb, Grp(F.Id("C")), Comma, F.Id("E"), Close, CloseBracket,
        Comma, RowBreak, Sp,
        Forall, Sp, F.Id("A"), Comma, F.Id("B"), Colon, Sp, F.Id("E"), To,
        Underscore, Grp(Mathbb, Grp(F.Id("C"))), F.Id("E"), Comma, Esc,
        Forall, Sp, Psi, InMacro, Sp, F.Id("E"), Comma, Esc,
        Operatorname, Grp(F.Id("IsSymmetric")), Open, F.Id("A"), Close,
        Sp, Land, Sp,
        Operatorname, Grp(F.Id("IsSymmetric")), Open, F.Id("B"), Close,
        Sp, Land, Sp, Vert, Sp, Psi, Vert, Eq, D(1), Sp, Rightarrow, Sp,
        RowBreak, Sp,
        Open, F.Id("u"), Colon, Eq, F.Id("A"), Psi, Minus, Langle, Sp, Psi,
        Comma, Sp, F.Id("A"), Psi, Rangle, Underscore,
        Grp(Mathbb, Grp(F.Id("C"))), Cdot, Sp, Psi, Close, Sp, Land, Sp,
        Open, F.Id("v"), Colon, Eq, F.Id("B"), Psi, Minus, Langle, Sp, Psi,
        Comma, Sp, F.Id("B"), Psi, Rangle, Underscore,
        Grp(Mathbb, Grp(F.Id("C"))), Cdot, Sp, Psi, Close, Sp, Land, Sp,
        RowBreak, Sp,
        Open, Operatorname, Grp(F.Id("Cov")), Colon, Eq,
        Frac, Grp(D(1)), Grp(D(2)), Cdot, Sp,
        Operatorname, Grp(F.Id("re")), Open, Langle, Sp, Psi, Comma, Sp,
        Open, F.Id("A"), F.Id("B"), Plus, F.Id("B"), F.Id("A"), Close,
        Psi, Rangle, Underscore, Grp(Mathbb, Grp(F.Id("C"))), Close,
        Minus, Operatorname, Grp(F.Id("re")), Open, Langle, Sp, Psi, Comma, Sp,
        F.Id("A"), Psi, Rangle, Underscore, Grp(Mathbb, Grp(F.Id("C"))), Close,
        Cdot, Operatorname, Grp(F.Id("re")), Open, Langle, Sp, Psi, Comma, Sp,
        F.Id("B"), Psi, Rangle, Underscore, Grp(Mathbb, Grp(F.Id("C"))), Close,
        Close, Sp, Land, Sp,
        RowBreak, Sp,
        Open, F.Id("c"), Colon, Eq, Frac, Grp(D(1)), Grp(D(2), F.Id("i")),
        Langle, Sp, Psi, Comma, Sp, Open, F.Id("A"), F.Id("B"), Minus,
        F.Id("B"), F.Id("A"), Close, Psi, Rangle, Underscore,
        Grp(Mathbb, Grp(F.Id("C"))), Close, Sp, Land, Sp,
        RowBreak, Sp,
        Open, F.Id("G"), Colon, Eq, Vert, Sp, F.Id("u"), Vert, Caret, Grp(D(2)),
        Cdot, Sp, Vert, Sp, F.Id("v"), Vert, Caret, Grp(D(2)), Minus,
        Vert, Langle, Sp, F.Id("u"), Comma, Sp, F.Id("v"), Rangle, Underscore,
        Grp(Mathbb, Grp(F.Id("C"))), Vert, Caret, Grp(D(2)), Close,
        Sp, Rightarrow, Sp,
        RowBreak, Sp,
        Vert, Sp, F.Id("u"), Vert, Caret, Grp(D(2)), Cdot, Sp,
        Vert, Sp, F.Id("v"), Vert, Caret, Grp(D(2)), Eq,
        Operatorname, Grp(F.Id("Cov")), Caret, Grp(D(2)), Plus,
        Vert, Sp, F.Id("c"), Vert, Caret, Grp(D(2)), Plus, F.Id("G"),
        Sp, Land, Sp, F.Id("G"), Sp, Geq, Sp, D(0), Sp, Land, Sp,
        RowBreak, Sp,
        Operatorname, Grp(F.Id("re")), Open, Langle, Sp, F.Id("u"), Comma, Sp,
        F.Id("v"), Rangle, Underscore, Grp(Mathbb, Grp(F.Id("C"))), Close,
        Eq, Operatorname, Grp(F.Id("Cov")), Sp, Land, Sp,
        Operatorname, Grp(F.Id("ofReal")), Open,
        Operatorname, Grp(F.Id("im")), Open, Langle, Sp, F.Id("u"), Comma, Sp,
        F.Id("v"), Rangle, Underscore, Grp(Mathbb, Grp(F.Id("C"))), Close, Close,
        Eq, F.Id("c"), Dot, Sp,
        End, Grp(F.Id("gathered"))));
}
