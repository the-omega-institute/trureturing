using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class KBonacciDirectSupportObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A given complex encoder supported on legal direct concatenations obeys every total-row rank bound.",
        H("Total spectral rows and direct concatenation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-encoder-spectral-obstruction"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/KBonacciDirectSupportObstruction.actual_encoder_spectral_obstruction"),
                H("The necessary spectral and threshold bounds"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Model(), Counts(), Contract(), Main()]))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "All coordinate spaces are the actual finite word spaces. W(m) is Fin m to Bool, "
                        + "L(k,m,w) is DBonacciAdmissible k m w, and append(x,y) is Fin.append x y. "
                        + "head(w) means (List.ofFn w).head?. The initial run p(w) is "
                        + "(List.ofFn w).findIdx Bool.not; t(w) is p of i mapped to w(Fin.rev i). "
                        + "An all-true word contributes its entire width. Natural subtraction is truncated at zero.")),
                    Paragraph(Text(
                        "P(N,b) is the actual bounded prime or nonprime integer page. Its cardinality is M(b), "
                        + "and orderIsoOfFin gives its increasing enumeration from Fin M(b). The logical carrier "
                        + "is the dependent sum of these pages. K(m,b) is the finite set of legal words with "
                        + "optional first bit some b; c(m,b) is its cardinality. Pi(b) is the logical diagonal "
                        + "page indicator and Q(m,b) is the diagonal indicator of K(m,b) in all words W(m). "
                        + "sigma(b) denotes the underlying complex matrix of a DensityState W(mX), "
                        + "namely CStarMatrix.ofMatrix.symm of its value.")),
                    Paragraph(Text(
                        "C(J,sigma) includes isometry, both physical page projection identities, density support, "
                        + "the exact identity for every logical matrix, and vanishing illegal amplitude for every "
                        + "logical vector. E and lambda are the eigenvectorBasis and eigenvalues of the Hermitian "
                        + "proof obtained from positivity of that actual sigma(b). D is the nonzero eigenvalue "
                        + "subtype. The displayed rank is Matrix.rank and dim is Module.finrank over Complex.")),
                    Paragraph(Text(
                        "The matrix-unit contract restricts the given J to the actual Y page before spectral "
                        + "contraction. A zero eigenvalue has zero contraction by the kernel identity for the "
                        + "actual column Gram matrix. Orthonormal spectral expansion reconstructs each total row. "
                        + "The weighted row Gram matrix is the positive diagonal spectrum, so all rows span D. "
                        + "Removing the a(s) earlier rows loses at most a(s) dimensions. Every remaining total row "
                        + "maps into B(s); the extracted isometry then forces M(true) dim V(s) at most n(s). "
                        + "This uses total amplitudes and permits cancellation between spectral terms.")),
                    Paragraph(Text(
                        "This is a necessary bound for an arbitrary given encoder. It does not characterize "
                        + "feasibility of a specified page-one density matrix by its rank and does not assert "
                        + "attainment or an entropy endpoint. The two-page existence and simultaneous entropy "
                        + "construction require a separate joint choice of actual word labels."))),
                DescribeRole.Theorem))));

    private static Formula Model()
    {
        return And(
            Eqn(Fn("W", Id("m")), Seq(OpCall("Fin", Id("m")), Sp, To, Sp, Op("Bool"))),
            Eqn(Fn("P", Id("N"), Id("b")), SetOf(Id("n"), OpCall("Fin", Seq(Id("N"), Plus, D(1))),
                Eqn(OpCall("decide", OpCall("NatPrime", OpCall("val", Id("n")))), Id("b")))),
            Eqn(Id("HL"), Seq(Sub(Sigma, Seq(Id("b"), Colon, Op("Bool"))), Sp, Fn("P", Id("N"), Id("b")))),
            Eqn(Fn("M", Id("b")), Card(Fn("P", Id("N"), Id("b")))),
            Eqn(Fn("K", Id("m"), Id("b")), SetOf(Id("w"), Fn("W", Id("m")), And(
                Fn("L", Id("k"), Id("m"), Id("w")),
                Eqn(OpCall("head", Id("w")), OpCall("some", Id("b")))))),
            Eqn(Fn("c", Id("m"), Id("b")), Card(Fn("K", Id("m"), Id("b")))));
    }

    private static Formula Counts()
    {
        return And(
            Eqn(Fn("x", Id("s")), Card(SetOf(Id("w"), Fn("K", Id("mX"), Op("true")),
                Eqn(Fn("t", Id("w")), Id("s"))))),
            Eqn(Fn("a", Id("s")), Seq(Sub(Sum, Seq(Id("u"), Lt, Id("s"))), Fn("x", Id("u")))),
            Eqn(Fn("B", Id("s")), SetOf(Id("y"), Fn("K", Id("mY"), Op("true")),
                Rel(Fn("p", Id("y")), Lt, Seq(Id("k"), Minus, Id("s"))))),
            Eqn(Fn("n", Id("s")), Card(Fn("B", Id("s")))),
            Eqn(Id("D0"), OpCall("min", Fn("c", Id("mX"), Op("false")),
                OpCall("NatDiv", Fn("c", Id("mY"), Op("false")), Fn("M", Op("false"))))),
            Eqn(Id("dstar"), OpCall("min", Fn("c", Id("mX"), Op("true")),
                Seq(Sub(Op("min"), Seq(D(0), Leq, Id("s"), Lt, Id("k"))), Par(Seq(
                    Fn("a", Id("s")), Plus,
                    OpCall("NatDiv", Fn("n", Id("s")), Fn("M", Op("true")))))))));
    }

    private static Formula Contract()
    {
        var j = Id("J"); var sig = Fn("sigma", Id("b")); var pi = Fn("Pi", Id("b"));
        var qx = Fn("Q", Id("mX"), Id("b")); var qy = Fn("Q", Id("mY"), Id("b"));
        return Eqn(Fn("C", j, Id("sigma")), And(
            Eqn(Mul(Adj(j), j), Id("I")),
            All(Id("b"), Op("Bool"), And(
                Eqn(Mul(OpCall("kronecker", qx, Id("I")), j), Mul(j, pi)),
                Eqn(Mul(OpCall("kronecker", Id("I"), qy), j), Mul(j, pi)),
                Eqn(Mul(qx, sig, qx), sig))),
            All(Id("A"), OpCall("Matrix", Id("HL"), Id("HL"), Cplx),
                Eqn(OpCall("partialTraceRight", Mul(j, Id("A"), Adj(j))),
                    Seq(Sub(Sum, Seq(Id("b"), InMacro, Op("Bool"))),
                        Mul(OpCall("trace", Mul(pi, Id("A"))), sig)))),
            All(Id("psi"), Seq(Id("HL"), To, Cplx),
                All(Id("x"), Fn("W", Id("mX")), All(Id("y"), Fn("W", Id("mY")),
                    Imp(Seq(Neg, Sp, Fn("L", Id("k"), Seq(Id("mX"), Plus, Id("mY")),
                        OpCall("append", Id("x"), Id("y")))),
                        Eqn(OpCall("mulVec", j, Id("psi"), Par(Seq(Id("x"), Comma, Id("y")))), D(0))))))));
    }

    private static Formula Main()
    {
        var b = Id("b"); var r = Id("r"); var x = Id("x"); var y = Id("y"); var s = Id("s");
        var q = Fn("q", x, Id("j")); var w = Fn("Wmat", y, Par(Seq(r, Comma, Id("j"))));
        var rank = OpCall("rank", Fn("sigma", b)); var vs = Fn("V", s);
        var spectral = And(
            Eqn(Id("E"), OpCall("eigenvectorBasis", Fn("sigma", b))),
            Eqn(Id("lambda"), OpCall("eigenvalues", Fn("sigma", b))),
            Eqn(Id("D"), SetOf(Id("j"), Fn("W", Id("mX")), Rel(Fn("lambda", Id("j")), Neq, D(0)))),
            All(x, Fn("W", Id("mX")), All(Id("j"), Id("D"),
                Eqn(q, Mul(Seq(Sqrt, Grp(Fn("lambda", Id("j")))), Fn("E", Id("j"), x))))));
        var threshold = All(s, Nat, Imp(Rel(s, Lt, Id("k")), And(
            Eqn(Fn("Arows", s), SetOf(x, Fn("K", Id("mX"), Op("true")), Rel(s, Leq, Fn("t", x)))),
            Eqn(vs, OpCall("span", Cplx, OpCall("image", Id("q"), Fn("Arows", s)))),
            Rel(rank, Leq, Seq(Fn("a", s), Plus, OpCall("dim", vs))),
            All(r, Fn("P", Id("N"), b), All(Id("v"), Seq(Id("D"), To, Cplx),
                Imp(Rel(Id("v"), InMacro, vs), All(y, Fn("W", Id("mY")),
                    Imp(Seq(Neg, Par(Rel(y, InMacro, Fn("B", s)))),
                        Eqn(Seq(Sub(Sum, Seq(Id("j"), Sp, InMacro, Sp, Id("D"))), Mul(w, Fn("v", Id("j")))), D(0))))))),
            Rel(Mul(Fn("M", b), OpCall("dim", vs)), Leq, Fn("n", s)))));
        var result = And(
            Eqn(Mul(Adj(Id("Wmat")), Id("Wmat")), Id("I")),
            All(r, Fn("P", Id("N"), b), All(x, Fn("W", Id("mX")), All(y, Fn("W", Id("mY")),
                Eqn(Fn("J", Par(Seq(x, Comma, y)), Par(Seq(b, Comma, r))),
                    Seq(Sub(Sum, Seq(Id("j"), Sp, InMacro, Sp, Id("D"))), Mul(q, w)))))),
            All(r, Fn("P", Id("N"), b), All(Id("j"), Id("D"), All(y, Fn("W", Id("mY")),
                Imp(Seq(Neg, Par(Rel(y, InMacro, Fn("K", Id("mY"), b)))), Eqn(w, D(0)))))),
            Eqn(OpCall("span", Cplx, OpCall("image", Id("q"), Fn("K", Id("mX"), b))), Op("top")),
            Imp(Eqn(b, Op("true")), threshold),
            Rel(rank, Leq, OpCall("if", b, Id("dstar"), Id("D0"))));
        return All(Seq(Id("N"), Comma, Id("k"), Comma, Id("mX"), Comma, Id("mY")), Nat,
            Imp(And(Rel(D(2), Leq, Id("N")), Rel(D(2), Leq, Id("k")),
                Rel(D(1), Leq, Id("mX")), Rel(D(1), Leq, Id("mY"))),
                All(Id("J"), OpCall("Matrix", Tensor(Fn("W", Id("mX")), Fn("W", Id("mY"))), Id("HL"), Cplx),
                    All(Id("sigma"), Seq(Op("Bool"), To, OpCall("DensityState", Fn("W", Id("mX")))),
                        Imp(Fn("C", Id("J"), Id("sigma")), All(b, Op("Bool"),
                            OpCall("let", spectral,
                                Seq(Exists, Sp, Open, Id("Wmat"), Colon,
                                    OpCall("Matrix", Fn("W", Id("mY")), Tensor(Fn("P", Id("N"), b), Id("D")), Cplx),
                                    Close, Comma, Sp, result))))))));
    }

    private static Formula Seq(params Formula[] xs) => F.Seq([.. xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Sp, x })]);
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Cplx => Seq(Mathbb, Grp(Id("C")));
    private static Formula Id(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(Id(name)));
    private static Formula Fn(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula OpCall(string name, params Formula[] args) => new Formula.Apply(Op(name), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Rel(Formula x, Formula op, Formula y) => Seq(x, Sp, op, Sp, y);
    private static Formula Eqn(Formula x, Formula y) => Rel(x, Eq, y);
    private static Formula Sub(Formula x, Formula i) => new Formula.Subscript(x, i);
    private static Formula Sup(Formula x, Formula i) => new Formula.Power(x, i);
    private static Formula Adj(Formula x) => Sup(x, Op("dagger"));
    private static Formula Mul(params Formula[] xs) => Seq([.. xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Sp, Cdot, Sp, x })]);
    private static Formula Tensor(Formula x, Formula y) => Seq(x, Sp, Times, Sp, y);
    private static Formula Card(Formula x) => Seq(Bar, x, Bar);
    private static Formula SetOf(Formula x, Formula type, Formula law) => Seq(OpenBrace, x, Colon, type, Sp, Bar, Sp, law, CloseBrace);
    private static Formula All(Formula x, Formula type, Formula law) => Par(Seq(Forall, Sp, Open, x, Colon, type, Close, Comma, Sp, Par(law)));
    private static Formula Imp(Formula x, Formula y) => Par(Rel(Par(x), Implies, Par(y)));
    private static Formula And(params Formula[] xs) => Par(Seq([.. xs.SelectMany((x, i) => i == 0 ? new[] { Par(x) } : new[] { Sp, Land, Sp, Par(x) })]));
}
