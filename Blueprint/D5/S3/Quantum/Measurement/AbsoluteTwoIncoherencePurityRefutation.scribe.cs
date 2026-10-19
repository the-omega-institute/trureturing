using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class AbsoluteTwoIncoherencePurityRefutationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation";
    private static readonly LibraryNoteRef Paper = LibraryNoteRef.Create("D5/L/Eigenstructure/johnstonmoeinpereiraplosker2022incoherence");
    private static Formula X(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(params string[] names) => Seq([.. names.SelectMany((name, index) =>
        index == 0 ? new[] { X(name) } : new[] { Dot, X(name) })]);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula App(Formula function, params Formula[] args) =>
        Seq([function, .. args.SelectMany(arg => new[] { Sp, arg })]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute two-incoherence beyond the purity bound.",
        H("AbsoluteTwoIncoherencePurityRefutation"), Blocks(
            Describe.Lean(DescribeId.Create("isabsolutelykincoherent"), DeclarationHandle.Create(Owner + ".IsAbsolutelyKIncoherent"),
                H("IsAbsolutelyKIncoherent"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(X("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(X("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(X("rho"), Sp, Colon, Sp, App(X("Matrix"), Parenthesized(App(X("Fin"), X("n"))), Parenthesized(App(X("Fin"), X("n"))), Seq(Mathbb, Grp(F.Id("C")))))), Sp, Comma, Sp, Seq(App(X("IsAbsolutelyKIncoherent"), X("k"), X("rho")), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(App(Qualified("D5", "S3", "Quantum", "Entanglement", "GHZMeasureBiseparableBound", "IsDensity"), X("rho"))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(X("U"), Sp, Colon, Sp, App(X("Matrix"), Parenthesized(App(X("Fin"), X("n"))), Parenthesized(App(X("Fin"), X("n"))), Seq(Mathbb, Grp(F.Id("C")))))), Sp, Comma, Sp, Seq(Parenthesized(Seq(X("U"), Sp, InMacro, Sp, App(Qualified("Matrix", "unitaryGroup"), Parenthesized(App(X("Fin"), X("n"))), Seq(Mathbb, Grp(F.Id("C")))))), Sp, To, Sp, App(Qualified("D5", "S3", "Quantum", "Measurement", "FactorWidthTwoCone", "IsKIncoherentSum"), X("k"), Parenthesized(Seq(Seq(X("U"), Sp, Cdot, Sp, X("rho")), Sp, Cdot, Sp, App(X("star"), Parenthesized(X("U"))))))))))))))))),
                AssessedProvenance.FromLiterature(Paper),
                Blocks(Paragraph(Text("Definition 3, page 10: “A mixed quantum state ρ ∈ Mₙ⁺ is absolutely k-incoherent if UρU* ∈ I_{k,n} for all unitary matrices U ∈ Mₙ.” The matrix has positive semidefinite trace-one density, and every unitary conjugate is a finite sum of outer products of k-sparse vectors."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Owner + ".claim"),
                H("claim"), StatementSource.FromAuthor(Disp(Seq(X("claim"), Sp, Eq, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Paper),
                Blocks(Paragraph(Text("Section 5, page 17: “Theorem 7 gives a sufficient condition for absolute 2-incoherence that is also necessary in dimension n = 3. It is unclear whether or not it is necessary in dimension n = 4 or higher.” The natural number n ranges over dimensions at least four; purity is the real trace of the square."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Owner + ".result"),
                H("result"), StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("A density matrix in dimension five is absolutely two-incoherent and has purity strictly greater than one quarter. The rank of a squared-modulus Gram matrix is at most four, which separates the relevant unitary orbit from the trace-one locally positive matrices."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("jmpp-2022-absolute-two-incoherence-purity"),
                    ResolutionKind.Refuted)))));
    private static Formula ClaimBody() => Seq(Forall, Sp, Parenthesized(Seq(X("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Seq(Parenthesized(Seq(D(4), Sp, Leq, Sp, X("n"))), Sp, To, Sp, Seq(Forall, Sp, Parenthesized(Seq(X("rho"), Sp, Colon, Sp, App(X("Matrix"), Parenthesized(App(X("Fin"), X("n"))), Parenthesized(App(X("Fin"), X("n"))), Seq(Mathbb, Grp(F.Id("C")))))), Sp, Comma, Sp, Seq(Parenthesized(App(X("IsAbsolutelyKIncoherent"), D(2), X("rho"))), Sp, To, Sp, Seq(Seq(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(X("rho"), Sp, Cdot, Sp, X("rho")))), Dot, X("trace"))), Dot, X("re")), Sp, Leq, Sp, new Formula.Fraction(D(1), Parenthesized(Seq(Parenthesized(Seq(X("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(1)))))))));
}
