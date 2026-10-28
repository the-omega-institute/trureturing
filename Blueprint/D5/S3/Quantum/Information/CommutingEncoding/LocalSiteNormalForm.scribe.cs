using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.CommutingEncoding;

internal sealed class LocalSiteNormalFormDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/CommutingEncoding/LocalSiteNormalForm";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commuting qubit tensor operators have local commutation signs and diagonal or phased Pauli local forms.",
        H("Local forms of commuting qubit factors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-commutation-signs"),
                DeclarationHandle.Create(Module + ".local_commutation_signs"),
                H("Local factors commute or anticommute"),
                StatementSource.FromAuthor(Disp(LocalSigns())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose that every local factor U(a,j) is unitary and the complete tensor "
                        + "operators commute. Multiplicativity of tensor products identifies the "
                        + "tensor of U(a,j)U(b,j) with the tensor of U(b,j)U(a,j). This tensor is "
                        + "unitary and therefore nonzero. Choose a nonzero matrix entry, keep all "
                        + "coordinates except j fixed, and vary the row and column at j. The product "
                        + "of the fixed entries is nonzero, so cancellation shows that the two "
                        + "local products differ by a complex scalar c.")),
                    Paragraph(Text(
                        "Both local products have the same nonzero determinant. Taking the "
                        + "determinant of the proportionality equation multiplies that determinant "
                        + "by c raised to the cardinality of Fin 2, namely c². Hence c² = 1, so "
                        + "c is 1 or −1. These give respectively commutation and anticommutation "
                        + "at every site j. The statement also permits n = 0, when there is no site j."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("local-site-normal-form"),
                DeclarationHandle.Create(Module + ".local_site_normal_form"),
                H("A diagonal or phased Pauli family"),
                StatementSource.FromAuthor(Disp(SiteNormalForm())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let B be any family of unitary two-by-two complex matrices, with each "
                        + "pair commuting or anticommuting. No finiteness or nonemptiness of the "
                        + "index type κ is required. First suppose a nonscalar member A has nonzero "
                        + "trace. If A anticommutes with B(a), conjugating A by B(a) negates A. "
                        + "Trace invariance then forces its trace to vanish, a contradiction. "
                        + "Thus every B(a) commutes with A. Diagonalize the normal matrix A by a "
                        + "unitary K. Its eigenvalues are distinct, because equality would make A "
                        + "scalar. The commutation equations for KᴴB(a)K force both off-diagonal "
                        + "entries to vanish. Taking V = Kᴴ gives the first alternative.")),
                    Paragraph(Text(
                        "Otherwise every nonscalar member is traceless. A unitary diagonalization "
                        + "then has eigenvalues c and −c, with star(c)c = 1. Conjugating Z back "
                        + "shows that each such matrix is c times a Hermitian involution. A scalar "
                        + "member is a unit-modulus scalar times the identity, so choose B(a) = c(a)H(a) "
                        + "for every a. All c(a) are nonzero; cancellation transfers each pair's "
                        + "commutation sign to the Hermitian involutions H(a).")),
                    Paragraph(Text(
                        "If all H(a) are scalar, use the identity unitary. Otherwise diagonalize "
                        + "a nonscalar H(a₀). Its distinct eigenvalues square to one and therefore "
                        + "are 1 and −1, so a unitary sends it to Z or −Z. Every transformed H(a) "
                        + "now commutes or anticommutes with Z. If they all commute with Z, their "
                        + "off-diagonal entries vanish, and squaring to the identity shows that "
                        + "they commute or anticommute with X as well. If some transformed H(b) "
                        + "anticommutes with Z, it has zero diagonal and off-diagonal entries z "
                        + "and star(z), where z star(z) = 1. The diagonal unitary with entries "
                        + "1 and z fixes Z and sends H(b) to X. Conjugating the sign relations "
                        + "with H(b) gives the signs with X for all other members.")),
                    Paragraph(Text(
                        "Finally a matrix squaring to the identity that has a commutation sign "
                        + "with both Z and X is a scalar multiple of a Pauli matrix. The four sign "
                        + "pairs give I, Z, X and Y; their scalar squares equal one and hence their "
                        + "scalars have unit modulus. Apply this to each transformed H(a), choose "
                        + "the Pauli label p(a), and multiply its scalar by the original phase c(a). "
                        + "The product phases still satisfy star(c(a))c(a) = 1. This gives the "
                        + "second alternative with one common unitary V."))),
                DescribeRole.Lemma))));

    private static Formula LocalSigns() => All("n", Nat, All("U", Encoders,
        Imp(All("a", Labels, All("j", Sites, Member(U("a", "j"), QubitUnitaries))),
            Imp(All("a", Labels, All("b", Labels, Equal(
                    Multiply(Tensor(Apply(V("U"), V("a"))), Tensor(Apply(V("U"), V("b")))),
                    Multiply(Tensor(Apply(V("U"), V("b"))), Tensor(Apply(V("U"), V("a"))))))),
                All("a", Labels, All("b", Labels, All("j", Sites,
                    Signs(U("a", "j"), U("b", "j")))))))));

    private static Formula SiteNormalForm()
    {
        Formula conjugate = Multiply(Multiply(V("V"), Apply(V("B"), V("a"))),
            QualifiedCall(["Matrix", "conjTranspose"], V("V")));
        Formula diagonal = All("a", Kappa, Some("d", Arrow(Call("Fin", D(2)), Complex),
            Equal(conjugate, QualifiedCall(["Matrix", "diagonal"], V("d")))));
        Formula pauli = Some("c", Arrow(Kappa, Complex), Some("p", Arrow(Kappa, Pauli),
            And(All("a", Kappa, Equal(
                    Multiply(Call("star", Apply(V("c"), V("a"))), Apply(V("c"), V("a"))), Typed(D(1), Complex))),
                All("a", Kappa, Equal(conjugate, QualifiedCall(["SMul", "smul"],
                    Apply(V("c"), V("a")), QualifiedCall(
                        ["D5", "S3", "Quantum", "Information", "StabilizerPairLocalUnitaryInequivalence", "pauliMatrix"],
                        Apply(V("p"), V("a")))))))));
        return All(Kappa, Seq(V("Type"), Star), All("B", Arrow(Kappa, Qubit),
            Imp(All("a", Kappa, Member(Apply(V("B"), V("a")), QubitUnitaries)),
                Imp(All("a", Kappa, All("b", Kappa, Signs(Apply(V("B"), V("a")), Apply(V("B"), V("b"))))),
                    Some("V", Qubit, And(Member(V("V"), QubitUnitaries), Or(diagonal, pauli)))))));
    }

    private static Formula U(string a, string j) => Apply(V("U"), V(a), V(j));
    private static Formula Signs(Formula a, Formula b) => Or(Equal(Multiply(a, b), Multiply(b, a)),
        Equal(Multiply(a, b), new Formula.Negate(Parenthesized(Multiply(b, a)))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Sites => Call("Fin", V("n"));
    private static Formula Labels => Call("Fin", new Formula.Power(D(2), V("n")));
    private static Formula Qubit => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Complex);
    private static Formula Encoders => Arrow(Labels, Arrow(Sites, Qubit));
    private static Formula QubitUnitaries => QualifiedCall(["Matrix", "unitaryGroup"], Call("Fin", D(2)), Complex);
    private static Formula Pauli => Qualified("D5", "S3", "Quantum", "Information", "StabilizerPairLocalUnitaryInequivalence", "Pauli");
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Typed(Formula body, Formula type) => Parenthesized(Seq(body, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) => All(V(name), type, body);
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Qualified(params string[] names) => Seq(Operatorname, Grp(Seq(
        [.. names.SelectMany((name, i) => i == 0 ? new[] { V(name) } : new[] { Dot, V(name) })])));
    private static Formula QualifiedCall(string[] names, params Formula[] args) => Apply(Qualified(names), args);
    private static Formula Tensor(Formula factors) => QualifiedCall(
        ["D5", "S3", "Quantum", "Information", "StabilizerPairLocalUnitaryInequivalence", "tensorOp"], factors);
}
