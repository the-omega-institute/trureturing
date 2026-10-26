using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzSpectralCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual support coordinates of Petz recovery.",
        H("Actual support coordinates of Petz recovery"), Blocks(
            Describe.Lean(
                DescribeId.Create("cfc-spectral-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzSpectralCoordinates.cfc_spectral_sum"),
                H("Hermitian spectral sum"), StatementSource.FromAuthor(Disp(CfcSpectralSum())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("For a finite Hermitian matrix, continuous functional calculus is the sum of the eigenvalue function applied to each eigenvalue times the corresponding rank-one eigenvector matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spectral-petz-coordinate-matrix"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzSpectralCoordinates.spectral_petz_coordinate_matrix"),
                H("Inverse-square-root modular coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("The positive-support relative modular coordinate matrix at B^(-1/2) eta is exactly "
                        + "Q^(-1/2) sqrt(T), using the spectral pseudoinverse on the kernel. The proof handles "
                        + "repeated eigenvalues and actual finite CFC coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-input-support-columns"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzSpectralCoordinates.petz_input_support_columns"),
                H("Reconstruct the input support columns"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("The positive input eigenbasis coordinate identities imply sqrt(S) Psi(Y) P_R = sqrt(R). "
                        + "The actual input kernel containment supplies the zero-eigenvalue coordinates. This "
                        + "supported identity is consumed by Schwarz trace rigidity; it is not promoted to an "
                        + "unsupported full-space equality."))),
                DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names) => Seq(Operatorname,
        Grp(Seq([.. names.SelectMany((name, index) => index == 0
            ? new Formula[] { X(name) } : new Formula[] { Dot, X(name) })])));
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arr(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Smul(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Cdot, Sp, Parenthesized(right));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula OfReal(Formula value) => At(Q("Complex", "ofReal"), value);
    private static Formula Star(Formula value) => At(Q("star"), value);
    private static Formula Sumf(string variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(variable), type)), Sp, Parenthesized(body));
    private static Formula Inst(string cls, Formula type) => Seq(OpenBracket, At(Q(cls), type), CloseBracket, Sp);
    private static Formula Types => Q("Type");
    private static Formula Reals => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(X("C")));
    private static Formula Matrix(Formula n) => At(Q("Matrix"), n, n, Complexes);
    private static Formula Fn(string variable, Formula type, Formula body) =>
        Seq(Q("fun"), Sp, Typed(X(variable), type), Sp, Mapsto, Sp, body);
    private static Formula CfcSpectralSum()
    {
        var eigenvalue = At(Q("Matrix", "IsHermitian", "eigenvalues"), X("hH"), X("i"));
        var vector = Fn("x", X("n"), At(Q("Matrix", "IsHermitian", "eigenvectorBasis"), X("hH"), X("i"), X("x")));
        var summand = Smul(OfReal(At(X("f"), eigenvalue)),
            At(Q("Matrix", "vecMulVec"), vector, Star(vector)));
        return All("n", Types, Seq(Inst("Fintype", X("n")), Inst("DecidableEq", X("n")),
            All("H", Matrix(X("n")),
                All("hH", At(Q("Matrix", "IsHermitian"), X("H")),
                    All("f", Arr(Reals, Reals),
                        Eqn(At(Q("cfc"), X("f"), X("H")), Sumf("i", X("n"), summand)))))));
    }
}
