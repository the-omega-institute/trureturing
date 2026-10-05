using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class KBonacciDirectRankEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Legal direct two-page concatenation has exact auxiliary ranks and simultaneous entropy maxima.",
        H("Exact ranks and entropy for direct concatenation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-original-direct-rank-entropy"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/KBonacciDirectRankEntropy.complete_original_direct_rank_entropy"),
                H("Two-page rank and entropy optimum"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Model(), Counts(), Contract(), Main()]))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "W(m) is the full Boolean computational word carrier Fin m to Bool. L(k,m,w) is the native "
                        + "DBonacciAdmissible predicate, append is Fin.append, and the first bit is (List.ofFn w).head?. "
                        + "The initial run p(w) is (List.ofFn w).findIdx Bool.not and the terminal run t(w) is p of "
                        + "the reversed word. All-true words contribute their full length, including windows shorter than k. "
                        + "The integer weights G(j) retain the powers-of-two initialization and k-term recurrence; the "
                        + "length-m interval normalization is G(m)=dbonacci(k,m+2). No address decoder is required by this regional encoder.")),
                    Paragraph(Text(
                        "P(N,b) consists of actual integers n at most N with decide(Nat.Prime n)=b. Its cardinality is M(b); "
                        + "orderIsoOfFin gives the original increasing page enumeration. Zero and one belong to page false, "
                        + "and two belongs to page true, so both logical pages are nonzero. HL is their dependent sum. "
                        + "K(m,b) consists of actual legal words with first bit b and c(m,b) is its cardinality. "
                        + "Pi and Q are the corresponding diagonal projections, embedded into the full computational spaces. "
                        + "NatDiv is integer floor division. The threshold minimum ranges over every state from zero to k-1.")),
                    Paragraph(Text(
                        "C(J,sigma) requires one complex isometry, both page projection identities, density support, "
                        + "the exact partial trace identity for every logical matrix A, and zero illegal amplitude for every "
                        + "logical vector psi. sigma(b) in the formulas is the complex matrix underlying DensityState W(mX). "
                        + "S is native vonNeumannEntropy, with natural logarithms and zero-log-zero equal to zero. "
                        + "A pure page vector has norm one and vanishes outside that logical page; SchmidtRank is the rank "
                         + "of its actual X-by-Y amplitude matrix. T is totalRowSpectralNecessity for the true page: it asserts the five true-page spectral reconstruction, support, span and threshold clauses defined in Lean. The separate two-page spectral result is supplied by KBonacciDirectSupportObstruction.actual_encoder_spectral_obstruction, not a literal expansion of T.")),
                    Paragraph(Text(
                        "The necessary bound uses the arbitrary positive spectrum and eigenvector basis of the given sigma. "
                        + "Its weighted computational rows q span the nonzero spectral coordinates. Removing a(s) low-state "
                        + "rows loses at most a(s) dimensions. The actual total row amplitudes map the remaining span into B(s), "
                        + "and the extracted isometry gives M(true) dim V(s) at most n(s). This includes cancellation between "
                        + "Schmidt terms. The neighborhoods are nested, with B(k-1) empty. The result gives no rank-only "
                        + "feasibility criterion for a density matrix whose eigenvectors were specified beforehand.")),
                    Paragraph(Text(
                        "For any positive ranks within the stated bounds, page-one X words are chosen by terminal state, "
                        + "then lexicographic order. Exactly max(0,d1-a(s)) selected rows have state at least s. "
                        + "Each selected row needs M(true) distinct labels. For a nonempty subset of these cloned demands, "
                        + "its minimum state identifies the union neighborhood B(s), and the threshold inequality bounds "
                        + "its cardinality. Hall's theorem supplies one jointly injective assignment of actual Y words. "
                        + "Page zero uses arbitrary distinct legal X words and M(false)d0 distinct legal Y words.")),
                     Paragraph(Text(
                         "The uniform construction combines both pages in the same ambient J. Its matrix units have "
                        + "partial trace delta(r,t)sigma(b) within a page and zero across pages, because the actual Y labels "
                        + "are globally distinct. Linear extension gives the identity for every matrix, and each chosen "
                        + "concatenation is legal, so all input amplitudes satisfy the support condition. The uniform "
                         + "pointer mixtures have ranks d0,d1 and entropies log(d0),log(d1). The actual nonzero density "
                         + "spectrum bounds every entropy by log(rank), proving both endpoints and the feasibility equivalence.")),
                     new DocumentBlock.DisplayFormula(Disp(TruePageT())),
                     Paragraph(Text(
                         "The stronger two-page spectral supplier is the existing theorem "
                         + "D5.S3.Quantum.Entanglement.KBonacciDirectSupportObstruction.actual_encoder_spectral_obstruction. "
                         + "The following display is explanatory supplier context with its own bound spectrum and page-dependent witness; it is not a literal unfolding of T and is not an additional authored assertion.")),
                     new DocumentBlock.DisplayFormula(Disp(Necessity())),
                     Paragraph(Text(
                         "UniformConstruction is the selected common witness for one permitted positive pair d0,d1. "
                         + "Its binders include the selected page-specific X words and one globally injective dependent-sum Y labeling; "
                         + "the identities below describe that selected witness only, while the capacity threshold is used only for s<k. "
                         + "complexDelta(u,v) is the complex Kronecker delta, invSqrt(d) is the complex scalar 1/sqrt(d), "
                         + "inv(d) is the complex scalar 1/d, and projector(w) is the computational pointer projector. "
                         + "The d1-a(s) subtraction is truncated natural subtraction.")),
                     new DocumentBlock.DisplayFormula(Disp(UniformConstruction()))),
                 DescribeRole.Theorem))));

    private static Formula Main()
    {
        var j = Id("J"); var sig = Id("sigma"); var b = Id("b");
        var rank0 = OpCall("rank", Fn("sigma", Op("false")));
        var rank1 = OpCall("rank", Fn("sigma", Op("true")));
        var jt = OpCall("Matrix", Tensor(Fn("W", Id("mX")), Fn("W", Id("mY"))), Id("HL"), Cplx);
        var st = Seq(Op("Bool"), To, OpCall("DensityState", Fn("W", Id("mX"))));
        var lower = And(Rel(D(1), Leq, Id("D0")), Rel(D(1), Leq, Id("dstar")));
        Formula Has(Formula law) => Par(Seq(Exists, Open, j, Colon, jt, Close,
            Open, sig, Colon, st, Close, Comma, And(Fn("C", j, sig), law)));
        Formula Each(Formula law) => All(j, jt, All(sig, st, Imp(Fn("C", j, sig), law)));
        var ranks = And(Eqn(rank0, Id("d0")), Eqn(rank1, Id("d1")));
        var positive = And(Rel(D(1), Leq, Id("d0")), Rel(Id("d0"), Leq, Id("D0")),
            Rel(D(1), Leq, Id("d1")), Rel(Id("d1"), Leq, Id("dstar")));
        var endpoints = Has(And(Eqn(rank0, Id("D0")), Eqn(rank1, Id("dstar")),
            Eqn(OpCall("S", Fn("sigma", Op("false"))), OpCall("log", Id("D0"))),
            Eqn(OpCall("S", Fn("sigma", Op("true"))), OpCall("log", Id("dstar")))));
        var result = And(
            Rel(D(0), Lt, Fn("M", Op("false"))), Rel(D(0), Lt, Fn("M", Op("true"))),
            Each(And(Rel(rank0, Leq, Id("D0")), Rel(rank1, Leq, Id("dstar")), Fn("T", j, sig))),
            All(Seq(Id("d0"), Comma, Id("d1")), Nat, Rel(Has(ranks), Iff, positive)),
            Rel(Has(Op("True")), Iff, lower),
            Each(All(b, Op("Bool"), All(Id("psi"), Seq(Id("HL"), To, Cplx),
                Imp(Fn("PurePage", b, Id("psi")),
                    Eqn(OpCall("SchmidtRank", j, Id("psi")), OpCall("rank", Fn("sigma", b))))))),
            Each(And(Rel(OpCall("S", Fn("sigma", Op("false"))), Leq, OpCall("log", Id("D0"))),
                Rel(OpCall("S", Fn("sigma", Op("true"))), Leq, OpCall("log", Id("dstar"))))),
            Imp(lower, endpoints));
        return All(Seq(Id("N"), Comma, Id("k"), Comma, Id("mX"), Comma, Id("mY")), Nat,
            Imp(And(Rel(D(2), Leq, Id("N")), Rel(D(2), Leq, Id("k")),
                Rel(D(1), Leq, Id("mX")), Rel(D(1), Leq, Id("mY"))), result));
    }

    private static Formula TruePageT()
    {
        var n = Id("N"); var k = Id("k"); var mx = Id("mX"); var my = Id("mY");
        var x = Id("x"); var y = Id("y"); var r = Id("r"); var j = Id("j"); var s = Id("s");
        var q = Fn("q", x, j); var w = Fn("Wmat", y, Par(Seq(r, Comma, j)));
        var threshold = Every("s", Nat, Imp(Rel(s, Lt, k),
            Let("Arows", OpCall("Set", Fn("W", mx)),
                SetOf(x, Fn("K", mx, Op("true")), Rel(s, Leq, Fn("t", x))),
                Let("V", OpCall("Submodule", Cplx, new Formula.TypeArrow(Id("D"), Cplx)),
                    OpCall("span", Cplx, OpCall("image", Id("q"), Id("Arows"))),
                    And(
                        Rel(OpCall("rank", Fn("sigma", Op("true"))), Leq,
                            Seq(Fn("a", s), Plus, OpCall("dim", Id("V")))),
                        Every("r", Fn("P", n, Op("true")), Every("v", new Formula.TypeArrow(Id("D"), Cplx),
                            Imp(Rel(Id("v"), InMacro, Id("V")), Every("y", Fn("W", my),
                                Imp(Seq(Neg, Par(Rel(y, InMacro, Fn("B", s)))),
                                    Eqn(Seq(Sub(Sum, Seq(j, InMacro, Id("D"))),
                                        Mul(w, Fn("v", j))), D(0))))))),
                        Rel(Mul(Fn("M", Op("true")), OpCall("dim", Id("V"))), Leq, Fn("n", s)))))));
        var clauses = And(
            Eqn(Mul(Adj(Id("Wmat")), Id("Wmat")), Id("I")),
            Every("r", Fn("P", n, Op("true")), Every("x", Fn("W", mx), Every("y", Fn("W", my),
                Eqn(Fn("J", Par(Seq(x, Comma, y)), Par(Seq(Op("true"), Comma, r))),
                    Seq(Sub(Sum, Seq(j, InMacro, Id("D"))), Mul(q, w)))))),
            Every("r", Fn("P", n, Op("true")), Every("j", Id("D"), Every("y", Fn("W", my),
                Imp(Seq(Neg, Par(Rel(y, InMacro, Fn("K", my, Op("true"))))), Eqn(w, D(0)))))),
            Eqn(OpCall("span", Cplx, OpCall("image", Id("q"), Fn("K", mx, Op("true")))), Op("top")),
            threshold);
        var definition = SpectralData(Op("true"), mx,
            Some("Wmat", OpCall("Matrix", Fn("W", my), Tensor(Fn("P", n, Op("true")), Id("D")), Cplx), clauses));
        return Ambient(n, k, mx, my,
            Every("J", EncoderType(n, mx, my), Every("sigma", PageStatesType(mx),
                Rel(Fn("T", Id("J"), Id("sigma")), Iff, definition))));
    }

    private static Formula UniformConstruction()
    {
        var n = Id("N"); var k = Id("k"); var mx = Id("mX"); var my = Id("mY");
        var b = Id("b"); var r = Id("r"); var j = Id("j"); var s = Id("s");
        var d0 = Id("d0"); var d1 = Id("d1"); var db = Fn("d", b);
        var bounds = And(Rel(D(2), Leq, n), Rel(D(2), Leq, k), Rel(D(1), Leq, mx), Rel(D(1), Leq, my));
        var positive = And(Rel(D(1), Leq, d0), Rel(d0, Leq, Id("D0")),
            Rel(D(1), Leq, d1), Rel(d1, Leq, Id("dstar")));
        var xType = Seq(Sub(Prod, Seq(b, Colon, Op("Bool"))),
            new Formula.TypeArrow(OpCall("Fin", db), Fn("W", mx)));
        var yIndex = Seq(Sub(Sigma, Seq(b, Colon, Op("Bool"))),
            Tensor(Fn("P", n, b), OpCall("Fin", db)));
        var y = Fn("Y", Par(Seq(b, Comma, r, Comma, j)));
        var xCondition = Every("b", Op("Bool"), And(
            OpCall("Injective", Fn("X", b)), Every("j", OpCall("Fin", db),
                Rel(Fn("X", b, j), InMacro, Fn("K", mx, b)))));
        var yCondition = And(OpCall("Injective", Id("Y")),
            Every("b", Op("Bool"), Every("r", Fn("P", n, b), Every("j", OpCall("Fin", db), And(
                Rel(y, InMacro, Fn("K", my, b)),
                Imp(Eqn(b, Op("true")), Rel(y, InMacro, Fn("B", Fn("t", Fn("X", b, j))))),
                Fn("DBonacciAdmissible", k, Seq(mx, Plus, my), OpCall("append", Fn("X", b, j), y)))))));
        var jIdentity = Every("b", Op("Bool"), Every("r", Fn("P", n, b),
            Every("x", Fn("W", mx), Every("y", Fn("W", my), Eqn(
                Fn("J", Par(Seq(Id("x"), Comma, Id("y"))), Par(Seq(b, Comma, r))),
                Mul(OpCall("invSqrt", db), Seq(Sub(Sum, Seq(j, Colon, OpCall("Fin", db))),
                    Mul(OpCall("complexDelta", Id("x"), Fn("X", b, j)),
                        OpCall("complexDelta", Id("y"), y)))))))));
        var sigmaIdentity = Every("b", Op("Bool"), Eqn(Fn("sigma", b),
            Mul(OpCall("inv", db), Seq(Sub(Sum, Seq(j, Colon, OpCall("Fin", db))),
                OpCall("projector", Fn("X", b, j))))));
        var selectedCount = Card(SetOf(j, OpCall("Fin", d1),
            Rel(s, Leq, Fn("t", Fn("X", Op("true"), j)))));
        var countIdentity = Every("s", Nat,
            Eqn(selectedCount, OpCall("max", D(0), Seq(d1, Minus, Fn("a", s)))));
        var thresholdUse = Every("s", Nat, Imp(Rel(s, Lt, k),
            Rel(Mul(Fn("M", Op("true")), selectedCount), Leq, Fn("n", s))));
        var witness = Let("d", new Formula.TypeArrow(Op("Bool"), Nat),
            Lam("b", Op("Bool"), OpCall("if", b, d1, d0)),
            Some("X", xType, Some("Y", new Formula.TypeArrow(yIndex, Fn("W", my)),
                And(xCondition, yCondition, Some("J", EncoderType(n, mx, my),
                    Some("sigma", PageStatesType(mx),
                        And(Fn("C", Id("J"), Id("sigma")), jIdentity, sigmaIdentity, countIdentity, thresholdUse)))))));
        return Ambient(n, k, mx, my, Imp(bounds,
            Every("d0", Nat, Every("d1", Nat, Imp(positive, witness)))));
    }

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

    private static Formula Necessity()
    {
        var n = Id("N"); var k = Id("k"); var mx = Id("mX"); var my = Id("mY");
        var b = Id("b"); var r = Id("r"); var x = Id("x"); var y = Id("y"); var j = Id("j"); var s = Id("s");
        var q = Fn("q", x, j); var w = Fn("Wmat", y, Par(Seq(r, Comma, j)));
        var rank = OpCall("rank", Fn("sigma", b));
        var threshold = Every("s", Nat, Imp(Rel(s, Lt, k),
            Let("Arows", OpCall("Set", Fn("W", mx)),
                SetOf(x, Fn("K", mx, Op("true")), Rel(s, Leq, Fn("t", x))),
                Let("V", OpCall("Submodule", Cplx, new Formula.TypeArrow(Id("D"), Cplx)),
                    OpCall("span", Cplx, OpCall("image", Id("q"), Id("Arows"))),
                    And(Rel(rank, Leq, Seq(Fn("a", s), Plus, OpCall("dim", Id("V")))),
                        Every("r", Fn("P", n, b), Every("v", new Formula.TypeArrow(Id("D"), Cplx),
                            Imp(Rel(Id("v"), InMacro, Id("V")), Every("y", Fn("W", my),
                                Imp(Seq(Neg, Par(Rel(y, InMacro, Fn("B", s)))),
                                    Eqn(Seq(Sub(Sum, Seq(j, InMacro, Id("D"))), Mul(w, Fn("v", j))), D(0))))))),
                        Rel(Mul(Fn("M", b), OpCall("dim", Id("V"))), Leq, Fn("n", s)))))));
        var result = And(Eqn(Mul(Adj(Id("Wmat")), Id("Wmat")), Id("I")),
            Every("r", Fn("P", n, b), Every("x", Fn("W", mx), Every("y", Fn("W", my),
                Eqn(Fn("J", Par(Seq(x, Comma, y)), Par(Seq(b, Comma, r))),
                    Seq(Sub(Sum, Seq(j, InMacro, Id("D"))), Mul(q, w)))))),
            Every("r", Fn("P", n, b), Every("j", Id("D"), Every("y", Fn("W", my),
                Imp(Seq(Neg, Par(Rel(y, InMacro, Fn("K", my, b)))), Eqn(w, D(0)))))),
            Eqn(OpCall("span", Cplx, OpCall("image", Id("q"), Fn("K", mx, b))), Op("top")),
            Imp(Eqn(b, Op("true")), threshold),
            Rel(rank, Leq, OpCall("if", b, Id("dstar"), Id("D0"))));
        return Ambient(n, k, mx, my,
            Imp(And(Rel(D(2), Leq, n), Rel(D(2), Leq, k), Rel(D(1), Leq, mx), Rel(D(1), Leq, my)),
                Every("J", EncoderType(n, mx, my), Every("sigma", PageStatesType(mx),
                    Imp(Fn("C", Id("J"), Id("sigma")), Every("b", Op("Bool"),
                        SpectralData(b, mx, Some("Wmat", OpCall("Matrix", Fn("W", my),
                            Tensor(Fn("P", n, b), Id("D")), Cplx), result))))))));
    }

    private static Formula SpectralData(Formula page, Formula mx, Formula body) =>
        Let("hPos", OpCall("PosSemidef", Fn("sigma", page)), OpCall("densityPositivity", Fn("sigma", page)),
            Let("E", OpCall("OrthonormalBasis", Fn("W", mx), new Formula.TypeArrow(Fn("W", mx), Cplx)),
                OpCall("eigenvectorBasis", OpCall("isHermitian", Id("hPos"))),
                Let("lambda", new Formula.TypeArrow(Fn("W", mx), Seq(Mathbb, Grp(Id("R")))),
                    OpCall("eigenvalues", OpCall("isHermitian", Id("hPos"))),
                    Let("D", Op("Type"), SetOf(Id("j"), Fn("W", mx), Rel(Fn("lambda", Id("j")), Neq, D(0))),
                        Let("q", new Formula.TypeArrow(Fn("W", mx), new Formula.TypeArrow(Id("D"), Cplx)),
                            Lam("x", Fn("W", mx), Lam("j", Id("D"),
                                Mul(OpCall("complexOfReal", Seq(Sqrt, Grp(Fn("lambda", OpCall("val", Id("j")))))),
                                    Fn("E", OpCall("val", Id("j")), Id("x"))))), body)))));

    private static Formula Ambient(Formula n, Formula k, Formula mx, Formula my, Formula body) =>
        Every("N", Nat, Every("k", Nat, Every("mX", Nat, Every("mY", Nat, body))));
    private static Formula EncoderType(Formula n, Formula mx, Formula my) =>
        OpCall("Matrix", Tensor(Fn("W", mx), Fn("W", my)),
            Seq(Sub(Sigma, Seq(Id("b"), Colon, Op("Bool"))), Fn("P", n, Id("b"))), Cplx);
    private static Formula PageStatesType(Formula mx) =>
        new Formula.TypeArrow(Op("Bool"), OpCall("DensityState", Fn("W", mx)));
    private static Formula Every(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
        OpCall("let", Eqn(Seq(Id(name), Colon, type), value), body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(Open, Id(name), Colon, type, Close, Mapsto, body);

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
