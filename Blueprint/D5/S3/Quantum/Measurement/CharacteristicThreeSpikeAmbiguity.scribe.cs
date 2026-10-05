using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class CharacteristicThreeSpikeAmbiguityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Quantum/zhu2026stable");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Flat-plus-spike states have uniformly nonvanishing characteristic-three ambiguity.",
        H("Characteristic-three flat-plus-spike ambiguity"),
        Blocks(
            Paragraph(Text(
                "Let K be any finite field with a decidable equality, q its cardinality, "
                + "s=sqrt(q), and N=2q+2s. The complex additive character psi is arbitrary. "
                + "All sums run over K. This is an ambiguity calculation on field labels; "
                + "no cyclic displacement or projector-Gram spectral identity is assumed.")),
            Node("spike-state", "The flat vector plus a spike", "spikeState", DescribeRole.Definition,
                Disp(Seq(Phi, Open, F.Id("x"), Close, Eq,
                    Frac, Grp(D(1), Plus, F.Id("s"), Indicator("x")),
                    Grp(Sqrt, Grp(F.Id("N"))))),
                "For every x in K, spikeState K x is (1+s if x=0, otherwise 1)/sqrt(N). "
                + "It equals (|+_q>+|0>)/sqrt(2+2/s), the phase-zero specialization of "
                + "Zhu–Wang equation (62). That equation is stated for characteristic two "
                + "in the paper; the characteristic-three bounds below are derived here."),
            Node("ambiguity", "The finite-character ambiguity coefficient", "ambiguity", DescribeRole.Definition,
                Disp(Seq(Apply("ambiguity", F.Id("psi"), F.Id("f"), F.Id("a"), F.Id("b")), Eq,
                    Sum, Underscore, Grp(F.Id("x"), Colon, F.Id("K")),
                    Overline, Grp(Apply("f", F.Id("x"))),
                    Apply("psi", Seq(F.Id("b"), Open, F.Id("x"), Minus, F.Id("a"), Close)),
                    Apply("f", Seq(F.Id("x"), Minus, F.Id("a"))))),
                "For every psi : AddChar K C, f : K -> C and a,b in K, "
                + "ambiguity is the displayed finite sum. This is <f,X_a Z_b f> with "
                + "X_a f(x)=f(x-a) and Z_b f(x)=psi(bx)f(x). Star is complex conjugation."),
            Node("normalization", "Coordinate normalization", "spikeState_normalized", DescribeRole.Theorem,
                Disp(Seq(Sum, Underscore, Grp(F.Id("x"), Colon, F.Id("K")),
                    NormSq(Seq(Phi, Open, F.Id("x"), Close)), Eq, D(1))),
                "For every finite field K, with no character or characteristic restriction, "
                + "the squared coordinate moduli of spikeState sum to one. "
                + "The unnormalized mass is q+2s+s^2=2q+2s."),
            Node("overlap", "The exact overlap", "spikeState_ambiguity", DescribeRole.Theorem,
                Disp(Seq(F.Id("A"), Open, F.Id("a"), Comma, F.Id("b"), Close, Eq,
                    Frac, Grp(F.Id("q"), Indicator("b"), Plus, F.Id("q"), Indicator("a"), Plus,
                        F.Id("s"), Open, D(1), Plus,
                        Apply("psi", Seq(Minus, F.Id("b"), F.Id("a"))), Close), Grp(F.Id("N")))),
                "For every finite field K, nontrivial psi (psi != 1 as an additive character), "
                + "and all a,b in K, A(a,b)=ambiguity psi (spikeState K) a b has this value. "
                + "Indicator(t) means 1 when t=0 and 0 otherwise. "
                + "The character sum uses Mathlib's sum_mulShift and IsPrimitive.of_ne_one. "
                + "The sign -ba follows from the field X_a Z_b convention."),
            Node("intensity", "Nonidentity intensity floor", "spikeState_intensity_lower_bound", DescribeRole.Theorem,
                Disp(Seq(Frac, Grp(D(1)),
                    Grp(D(4), Open, F.Id("s"), Plus, D(1), Close, Caret, Grp(D(2))), Le,
                    NormSq(Seq(F.Id("A"), Open, F.Id("a"), Comma, F.Id("b"), Close)))),
                "For every finite field K of characteristic three, every nontrivial psi, "
                + "and every a,b with a!=0 or b!=0, the displayed bound holds. "
                + "Off the axes psi(-ba)^3=1 implies |1+psi(-ba)|^2>=1. "
                + "On an axis the numerator is q+2s, which also meets the lower bound. "
                + "No Gram matrix or eigenvalue is defined by this theorem."),
            Node("uniform", "Uniform ambiguity-side SIC scale", "spikeState_uniform_ambiguity_bound", DescribeRole.Theorem,
                Disp(Seq(Sum, Underscore, Grp(F.Id("x"), Colon, F.Id("K")),
                    NormSq(Seq(Phi, Open, F.Id("x"), Close)), Eq, D(1), Land,
                    Frac, Grp(D(1)), Grp(D(8)), Le,
                    Open, F.Id("q"), Plus, D(1), Close,
                    NormSq(Seq(F.Id("A"), Open, F.Id("a"), Comma, F.Id("b"), Close)))),
                "For every finite field K of characteristic three, every nontrivial psi, "
                + "and every nonidentity label, the vector is normalized and (q+1)|A(a,b)|^2>=1/8. "
                + "The dimension-independent constant follows from (s-1)^2>=0. "
                + "This bounds normalized ambiguity intensities, not an assumed spectrum."),
            Paragraph(Text(
                "The formalized Gram/Rayleigh interface remains open: the target is "
                + "one unit vector on each F_(3^r), for every integer r>=1, "
                + "with one c>0 such that Re(w*G^Pi w) >= c q/(q+1) sum |w|^2 whenever sum w=0. "
                + "A canonical trace-character instantiation and a proved finite-field "
                + "Weyl/Fourier Gram identity are still required to use c=1/8. "
                + "This module proves neither the target family Rayleigh bound nor POVM completeness.")))));

    private static DocumentBlock Node(string id, string title, string declaration, DescribeRole role,
        Formula statement, string commentary) => Describe.Lean(
            DescribeId.Create("char-three-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(commentary))), role);

    private static Formula Indicator(string variable) =>
        Seq(Operatorname, Grp(F.Id("indicatorZero")), Open, F.Id(variable), Close);

    private static Formula NormSq(Formula value) =>
        Seq(Vert, Sp, value, Sp, Vert, Caret, Grp(D(2)));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var parts = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) parts.Add(Comma);
            parts.Add(arguments[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }
}
