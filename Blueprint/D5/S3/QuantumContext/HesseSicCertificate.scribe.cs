using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class HesseSicCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nine explicit qutrit vectors form the dimension-three Hesse SIC configuration.",
        H("The Dimension-Three Hesse SIC Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hesse-sic-certificate"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumContext/HesseSicCertificate.hesse_sic_certificate"),
                H("Nine Hesse vectors have constant overlap and resolve the identity"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let omega=exp(2 pi i/3). For k=0,1,2, the nine vectors are "
                            + "(0,1,-omega^k)/sqrt(2), (-omega^k,0,1)/sqrt(2), and "
                            + "(1,-omega^k,0)/sqrt(2), in that order. The Lean definitions "
                            + "hesseVector and hesseKet give these coordinates as functions on "
                            + "Fin 9 and as vectors in the complex Euclidean space on Fin 3.")),
                    Paragraph(Text(
                        "Every vector has two coordinates of modulus one over sqrt two, so its "
                            + "squared norm is one. Within one support block, the complete "
                            + "off-diagonal table reduces to 1+omega or 1+omega^2, up to a unit "
                            + "phase. Across blocks, two vectors meet in exactly one coordinate. "
                            + "The squared modulus is therefore exactly one quarter for every "
                            + "distinct ordered pair.")),
                    Paragraph(Text(
                        "For the rank-one projector sum, each diagonal entry receives six "
                            + "contributions of one half and is therefore three. Each off-diagonal "
                            + "entry is minus one half times 1+omega+omega^2, or its conjugate, and "
                            + "vanishes. Thus all nine matrix entries agree with three times the "
                            + "three-dimensional identity matrix.")),
                    Paragraph(Text(
                        "The Lean proof evaluates the full finite tables from the displayed "
                            + "coordinates and proves the required cube-root identities from the "
                            + "complex exponential. It uses no numerical approximation, frozen "
                            + "D5 theorem, unchecked evaluator, private axiom, or restatement of "
                            + "the dimension-twenty-four Zauner modular certificate."))),
                DescribeRole.Theorem))));

    private static Formula CertificateFormula()
    {
        Formula finNine = Call(F.Id("Fin"), D(9));
        Formula first = F.Id("r");
        Formula second = F.Id("s");
        Formula firstVector = Subscript(F.Id("v"), first);
        Formula secondVector = Subscript(F.Id("v"), second);

        return Disp(Seq(
            Forall, Sp, first, Colon, Sp, finNine, Comma, Esc,
            VectorNormSquared(firstVector), Sp, Eq, Sp, D(1), Comma, RowBreak,
            Land, Sp, Open, Forall, Sp, first, Comma, Sp, second, Colon, Sp, finNine,
            Comma, Esc, first, Sp, Neq, Sp, second, Sp, Rightarrow, Sp,
            AbsSquared(InnerProduct(firstVector, secondVector)), Sp, Eq, Sp,
            Frac, Grp(D(1)), Grp(D(4)), Close, Comma, RowBreak,
            Land, Sp, Sum, Underscore, Grp(first, Colon, Sp, finNine), Sp,
            firstVector, Sp, ConjugateTranspose(firstVector), Sp, Eq, Sp,
            D(3), Sp, Subscript(F.Id("I"), D(3)), Dot));
    }

    private static Formula Call(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula VectorNormSquared(Formula value) =>
        Seq(new Formula.Norm(value), Caret, Grp(D(2)));

    private static Formula AbsSquared(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert, Caret, Grp(D(2)));

    private static Formula InnerProduct(Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle);

    private static Formula ConjugateTranspose(Formula value) =>
        Seq(value, Caret, Grp(Star));
}
