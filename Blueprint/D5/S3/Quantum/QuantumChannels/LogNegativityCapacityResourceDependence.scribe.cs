using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class LogNegativityCapacityResourceDependenceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.";
    private static readonly LibraryNoteRef Campbell = LibraryNoteRef.Create("D5/L/QuantumContext/campbell2010optimalentangling");
    private static readonly LibraryNoteRef Tiles = LibraryNoteRef.Create("D5/L/QuantumContext/bennett1999unextendible");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-qutrit CPTP map separates assisted and separable-input log-negativity capacities.",
        H("Log-negativity capacity depends on the input resource"),
        Blocks(
            Node("extend", "Free local ancillary systems", ExtendFormula(),
                "Section I, p. 2, verbatim: “Throughout, we assume that local ancilla (typically labelled as Hilbert space Ha′ ⊗ Hb′ ), local unitaries and classical communication are freely available as is appropriate in many communication and distributed computation scenarios.” The finite Kraus action is D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus applied to the two displayed families and rho. It uses identity Kraus factors on the ancillary pair, with Matrix.reindex ordering the cut as AA' versus BB'.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Campbell)),
            Node("capSep", "Separable-input entangling capacity", CapacityFormula(false),
                "Section I, Eq. (1), p. 2, verbatim: “The maximum achievable entanglement for a dynamical map, Λ, when the initial state is separable, is given by:” The formula is E(Λ) = sup{E(Λ(σ))|σ ∈ S}. Eqs. (4)–(5) and the logarithmic rescaling use Real.logb 2 of the partial-transpose trace norm. The supremum in EReal includes every finite local ancilla dimension. IsDensity is positive semidefinite with trace one, and IsSeparable is a finite convex mixture of products of such matrices.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Campbell)),
            Node("capAssisted", "Assisted entangling capacity", CapacityFormula(true),
                "Section I, Eq. (2), p. 2, verbatim: “However, when prior entanglement is available, the maximum increase of entanglement is:” The formula is Eᴰ(Λ) = sup{E(Λ(σ)) − E(σ)|σ ∈ D}. Both logarithms have base two. No restriction to positive partial transpose is imposed on these inputs.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Campbell)),
            Node("claim", "The all-CPTP resource-independence question", ClaimFormula(),
                "Section VII, p. 7, verbatim: “The most obvious open question is whether log-negativity EC is resource independent for all unitaries, or indeed all CPTP maps, or whether this is a singular feature of 2-qubit gates.” The assertion here is its all-CPTP clause. The dimensions dA and dB and the finite Kraus count r range over natural numbers. Completeness of the Kraus family states trace preservation. The two capacities include every finite local ancillary system.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Campbell)),
            Node("symKet", "The symmetric Bell vector", BellKetFormula(false),
                "The unnormalized vector has amplitude one at (0,1) and (1,0), and zero elsewhere in the two-qutrit space. Pi.single denotes a function supported at one index.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("antiKet", "The antisymmetric Bell vector", BellKetFormula(true),
                "The unnormalized vector has amplitude one at (0,1), minus one at (1,0), and zero elsewhere in the two-qutrit space. The two Bell vectors give the off-diagonal terms in the positive and negative parts of the Bell state's partial transpose.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("separable_ppt", "Separable states have positive partial transpose", SeparablePptFormula(),
                "For arbitrary finite types A and B, a finite convex mixture of product density matrices remains positive semidefinite after transposing the B indices. The matrix entry at (a,b),(c,d) is sigma((a,d),(c,b)). Positivity follows by applying partial transpose to each product and adding the nonnegative weighted terms.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("result", "A CPTP separation", Seq(Neg, Sp, Parenthesized(ClaimBody())),
                "The Tiles complementary projector Q is positive under partial transpose. The input Q/4 therefore has zero log-negativity and gives output partial-transpose trace norm two. For a separable input with arbitrary finite local ancillas, the conditional ancillary matrices are positive under partial transpose; a rational product-overlap estimate bounds the output norm by 2 minus 1/6561. The assisted capacity is at least one, whereas the separable-input capacity is at most log base two of 2 minus 1/6561, strictly less than one. This does not decide the question for unitary channels.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Campbell, Tiles),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("campbell-2010-log-negativity-resource-independence"), ResolutionKind.Refuted)))));
    private static DocumentBlock Node(string n, string title, Formula f, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("cam-" + n.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Owner + n), H(title),
            StatementSource.FromAuthor(Disp(f)), provenance, Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);
    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula At(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, Parenthesized(Seq(V(n), Sp, Colon, Sp, t)), Comma, Sp, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, b);
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula ProdType(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Sp, Colon, Sp, t));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula i, Formula j) => Call("Matrix", i, j, C);
    private static Formula Sq(Formula i) => Mat(i, i);
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(Seq(V(n), Sp, Colon, Sp, t)), Sp, Parenthesized(b));
    private static Formula Lam(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, Parenthesized(Seq(V(n), Sp, Colon, Sp, t)), Sp, Mapsto, Sp, b);
    private static Formula Kron(Formula a, Formula b) => Call("kronecker", a, b);
    private static Formula Adj(Formula a) => Call("conjTranspose", a);
    private static Formula BaseType => ProdType(Fin(V("dA")), Fin(V("dB")));
    private static Formula InputType => ProdType(ProdType(Fin(V("dA")), Fin(V("a"))), ProdType(Fin(V("dB")), Fin(V("b"))));
    private static Formula KrausType => Arrow(Fin(V("r")), Sq(BaseType));
    private static Formula ChannelInputs(Formula b) => All("dA", N, All("dB", N, All("r", N, All("K", KrausType, b))));
    private static Formula LogNeg(Formula x) => Call("logb", D(2), Call("traceNorm", Call("partialTranspose", x)));
    private static Formula SupOver(string n, Formula t, Formula b) => Seq(Seq(Operatorname, Grp(V("iSup"))), Underscore, Grp(Seq(V(n), Sp, Colon, Sp, t)), Sp, Parenthesized(b));
    private static Formula BellKetFormula(bool antisymmetric)
    {
        Formula pair = ProdType(Fin(D(3)), Fin(D(3)));
        Formula first = Call("single", Cast(Parenthesized(Seq(D(0), Comma, Sp, D(1))), pair), Cast(D(1), C));
        Formula second = Call("single", Cast(Parenthesized(Seq(D(1), Comma, Sp, D(0))), pair), Cast(D(1), C));
        Formula body = new Formula.Binary(first,
            antisymmetric ? FormulaBinaryOperator.Subtract : FormulaBinaryOperator.Add, second);
        return Eq(Cast(V(antisymmetric ? "antiKet" : "symKet"), Arrow(pair, C)), body);
    }
    private static Formula CapacityFormula(bool assisted)
    {
        Formula k = V("K"), rho = V("rho");
        Formula output = LogNeg(Call("extend", k, rho));
        Formula value = assisted ? Sub(output, LogNeg(rho)) : output;
        Formula premise = assisted ? Call("IsDensity", rho) : And(Call("IsDensity", rho), Call("IsSeparable", rho));
        Formula objective = Seq(Seq(Operatorname, Grp(V("iSup"))), Underscore, Grp(Parenthesized(premise)), Sp, Cast(Cast(value, R), V("EReal")));
        return ChannelInputs(Eq(Call(assisted ? "capAssisted" : "capSep", k),
            SupOver("a", N, SupOver("b", N, SupOver("rho", Sq(InputType), objective)))));
    }
    private static Formula ExtendFormula()
    {
        Formula k = V("K"), rho = V("rho"), i = V("k");
        Formula e = Call("prodProdProdComm", Fin(V("dA")), Fin(V("dB")), Fin(V("a")), Fin(V("b")));
        Formula family = Lam("k", Fin(V("r")), Call("reindex", e, e,
            Kron(At(k, i), Cast(D(1), Sq(ProdType(Fin(V("a")), Fin(V("b"))))))));
        Formula owner = Seq(Operatorname, Grp(V("D5"), Dot, V("S3"), Dot, V("Quantum"), Dot,
            V("Foundation"), Dot, V("FiniteKrausChannel"), Dot, V("PhyslibLeaf"), Dot,
            V("MatrixMap"), Dot, V("of")), Underscore, Grp(V("kraus")));
        return ChannelInputs(All("a", N, All("b", N, All("rho", Sq(InputType),
            Eq(Call("extend", k, rho), At(At(owner, family, family), rho))))));
    }
    private static Formula SeparablePptFormula()
    {
        Formula a = V("A"), b = V("B"), sigma = V("sigma");
        Formula pair = ProdType(a, b);
        Formula entry = Lam("i", pair, Lam("j", pair,
            At(sigma, Parenthesized(Seq(Call("fst", V("i")), Comma, Sp, Call("snd", V("j")))),
                Parenthesized(Seq(Call("fst", V("j")), Comma, Sp, Call("snd", V("i")))))));
        return All("A", V("Type"), All("B", V("Type"),
            All("finiteA", Call("Fintype", a), All("finiteB", Call("Fintype", b),
            All("eqA", Call("DecidableEq", a), All("eqB", Call("DecidableEq", b),
            All("sigma", Sq(pair), Imp(Call("IsSeparable", sigma), Call("PosSemidef", entry)))))))));
    }
    private static Formula ClaimFormula() => IffOf(V("claim"), ClaimBody());
    private static Formula ClaimBody()
    {
        Formula k = V("K");
        Formula complete = Eq(SumOver("k", Fin(V("r")), Mul(Adj(At(k, V("k"))), At(k, V("k")))), Cast(D(1), Sq(BaseType)));
        return ChannelInputs(Imp(complete, Eq(Call("capAssisted", k), Call("capSep", k))));
    }
}
