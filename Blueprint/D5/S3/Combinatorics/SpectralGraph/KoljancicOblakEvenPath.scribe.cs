using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class KoljancicOblakEvenPathDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/koljancic2026nssp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted branch continuants and their first variations for the even double-path nSSP question.",
        H("Even double paths with a nonempty loop set"), Blocks(
            Paragraph(Text("Koljančić and Oblak ask in Question 5.11 of arXiv:2604.21552v1 whether every even double path with at least one loop allows the non-symmetric Strong Spectral Property. Allows means existence of a real matrix with exactly the prescribed nonzero entries. The test matrix in the nSSP definition is an unrestricted real matrix, and the commutator uses its transpose.")),
            Paragraph(Text("The formal claim retains every positive even order and every nonempty loop set. It imposes no symmetry, sign, trace or spectral condition on the existential witness. The source convention on vertices numbered from one corresponds to Fin n by subtracting one.")),
            Node("pattern", "Exact double-path pattern", "pathPattern", DescribeRole.Definition,
                "Both orientations of each consecutive edge occur; the only additional arcs are the specified loops.", true),
            Node("nssp", "Non-symmetric Strong Spectral Property", "HasNSSP", DescribeRole.Definition,
                "Entrywise annihilation and the transpose commutator must force every real test matrix to vanish.", true),
            Node("claim", "Complete Question 5.11 event", "claim", DescribeRole.Definition,
                "This proposition is the full source question. The companion KoljancicOblakEvenPathNSSP.result proves it with exactly these quantifiers.", true),
            Node("continuant", "Zero-diagonal branch continuant", "continuant", DescribeRole.Definition,
                "The empty branch has polynomial one and a one-vertex branch has polynomial X. Each successor step uses the squared weight of the newly attached edge."),
            Node("variation", "Edge-parameter first variation", "variation", DescribeRole.Definition,
                "The formal linearized recurrence includes the variation of the edge parameter and the variation of the preceding continuant. The actual evaluated characteristic differential is supplied by joined_path_charpoly_derivative."),
            Node("deformation", "Simultaneous polynomial edge perturbation", "deformedContinuant", DescribeRole.Definition,
                "Each squared edge parameter is replaced by q plus z times dq. The outer polynomial variable is z; coefficients are polynomials in the spectral variable X. In its defining formula, z denotes the outer Polynomial.X and C embeds into the applicable polynomial ring."),
            Node("linearization", "Exact constant and first-order terms", "continuant_linearization", DescribeRole.Theorem,
                "The constant term of the deformation is the continuant and its coefficient of z is exactly variation. The induction uses the complete coefficient-one product rule, with both cross terms. This is algebraic first-order evidence for all lengths and all real parameter and variation sequences; it is not a claim that the complete central-vertex coefficient map is already injective.", formula: Linearization()),
            Node("recovery", "Reverse recovery of every edge variation", "branch_variation_injective", DescribeRole.Theorem,
                "At a nonzero edge-parameter sequence, two consecutive zero polynomial variations force every earlier edge variation to vanish. The leading coefficient of each continuant is one, while its variation has strictly smaller degree. Taking that coefficient in the linearized recurrence first recovers the last edge variation; cancellation and induction recover the remaining edges. Length-zero and length-one branches are included without extra parameters.", formula: Recovery()),
            Node("matrix", "Actual zero-diagonal weighted branch", "weightedPath", DescribeRole.Definition,
                "The two orientations of each edge carry the same real weight. Vertex reversal aligns the first-row determinant expansion with the last edge in the recurrence. The constructor permits zero weights as well. Subtraction in its natural-number edge index is truncated subtraction."),
            Node("characteristic", "Weighted branch characteristic correspondence", "weighted_path_charpoly", DescribeRole.Theorem,
                "The actual characteristic polynomial of the weighted branch equals the continuant with squared edge parameters, in every order including zero and one. First-row expansion uses the existing det_sparse_front supplier in ForbiddenNeighbourDeterminant; both remaining principal submatrices have the same reversed-edge convention.", formula: Characteristic()),
            Node("joined-variation", "Complete central-loop variation", "joinedVariation", DescribeRole.Definition,
                "Write U=P_left(r), V=P_right(s), F=XU-P_left(r+1), and G=XV-P_right(s+1). The displayed expression retains all six contributions to the variation of (X-a)UV-FV-UG. Each flux is zero when its branch is empty; for a positive branch length its flux is the attaching squared edge weight times the preceding continuant. The joined_path_charpoly theorem supplies the corresponding actual central-loop matrix characteristic expression; the matrix support-tangent bridge is separate.", formula: JoinedDefinition()),
            Node("joined-deformation", "Actual simultaneous algebraic perturbation", "deformedJoinedContinuant", DescribeRole.Definition,
                "Replace the central loop by a plus z times da and each branch squared edge parameter by q plus z times dq in the joined expression. The outer polynomial variable is z and the inner variable X is spectral. In the formula C embeds into the applicable coefficient ring. The complete coefficient-one product rule identifies this perturbation coefficient with joinedVariation; that identity is consumed in the recovery theorem.", formula: JoinedDeformation()),
            Node("joined-recovery", "Separation of central and branch variations", "joined_variation_injective", DescribeRole.Theorem,
                "For every pair of branch lengths with odd sum, nonzero central loop and nonzero branch edge parameters, coprime branch continuants make the coefficient of z in the actual algebraic joined perturbation injective. The recovered edge indices below each branch length include its attaching edge. No lower bound on either individual branch length is imposed. The complete product rule first identifies that coefficient with joinedVariation. Reflection X to -X then separates the odd part C(a) times the product variation plus C(da)UV. Its leading coefficient recovers da, after which coprimality and strict degree bounds separate both branch variations. Applying the same separation to the remaining adjacent continuants and using branch_variation_injective recovers all edge parameters. This theorem assumes coprimality; it does not construct the required branches or prove the complete nSSP claim.", formula: JoinedRecovery()),
            Node("coprime", "Uniform positive coprime branch construction", "coprime_positive_branches", DescribeRole.Theorem,
                "Every pair of lengths with odd sum admits two strictly positive squared-edge parameter sequences whose continuants are coprime. Put unit parameters on an even-length branch and a common positive parameter t on the other branch. The first branch has nonzero constant coefficient. The spectral resultant is a polynomial in t; at t=0 the other branch becomes X to its length, so the resultant is nonzero. A positive t outside its finite root set gives the required pair. Swapping the branches covers the other parity orientation. Zero and one lengths need no exceptions, and the final selected t is strictly positive; zero is used only to prove that the parameter polynomial is not identically zero.", formula: CoprimeBranches()),
            Node("joined-matrix", "Actual path with one central loop", "joinedPath", DescribeRole.Definition,
                "The vertex set is Fin(s+1+r), with the loop at vertex r. The left branch edges have weights bL(0) through bL(r-1) from its far endpoint towards the loop; the right branch edges have weights bR(s-1) down to bR(0) from the loop towards its far endpoint. All diagonal entries except the central loop are zero. Natural-number subtraction in the displayed edge indices is truncated subtraction. Empty branches, either endpoint and the single-vertex carrier are included.", formula: JoinedMatrixDefinition()),
            Node("joined-characteristic", "Actual central-loop characteristic identity", "joined_path_charpoly", DescribeRole.Theorem,
                "For every pair of real edge sequences, every real loop weight and every pair of natural branch lengths, the characteristic polynomial of joinedPath equals the displayed branch-continuant expression. This is also (X-C(a))UV-FV-UG with U=P_left(r), V=P_right(s), F=XU-P_left(r+1) and G=XV-P_right(s+1). The proof uses the actual matrix determinant, the frozen sparse determinant expansion, the existing weighted_path_charpoly, and induction from either empty or one-vertex left branches. The front recurrence for continuants aligns the far-end deletion with the squared edge indexing. The formula assumes neither nonzero weights nor parity, and includes every endpoint and empty branch. It does not establish the support-tangent or unrestricted commutant bridges.", formula: JoinedMatrixCharacteristic()),
            Node("matrix-derivative", "Actual characteristic variation along edge and loop perturbations", "joined_path_charpoly_derivative", DescribeRole.Theorem,
                "For every real edge and variation sequence, every loop weight and variation, every pair of natural branch lengths and every real spectral value x, the actual characteristic polynomial evaluated at x has the displayed derivative at perturbation parameter zero. Each edge is perturbed by b+t*db and the central loop by a+t*da. The squared-edge first variations are 2*b*db, with the complete joined product rule retained. The proof differentiates the continuant recurrence and applies joined_path_charpoly to the actual perturbed matrix. Zero edge weights, empty branches and endpoints remain included. The conditional application below uses these evaluated derivatives directly, together with an orthogonal diagonalization having distinct eigenvalues. It does not require a separate characteristic-coefficient or adjugate interface. The companion KoljancicOblakEvenPathNSSP.result supplies that diagonalization for the selected branch weights and constructs the final exact-support witnesses.", formula: JoinedMatrixDerivative()),
            Paragraph(Text("Conditional unrestricted commutant application. Let the two branch lengths have odd sum, let the loop and all r+s used edge weights be nonzero, and let the two squared-weight continuants be coprime. Suppose U is real orthogonal and U-transpose A U is diagonal with pairwise distinct diagonal entries, where A is the actual joinedPath. Under these explicit hypotheses the existing matrix derivative and recovery relations imply HasNSSP A. This conditional application supplies no existence assertion for U, the branch weights or the final exact-support witness.")),
            new DocumentBlock.DisplayFormula(NsspBridge()),
            Paragraph(Text("Put n=r+s+1. Parameterize a symmetric support tangent T(v) by its r left edges, one central loop and s right edges, so v lies in Real to the n. Its spectral diagonal readout is v mapped to diag(U-transpose T(v) U). If this readout vanishes, the derivative of every evaluated characteristic polynomial vanishes: the determinant differential at a diagonal matrix is a sum of determinants with one row replaced, and the zero diagonal of the direction leaves a zero column in each summand. Orthogonal conjugation preserves the characteristic polynomial. Applying joined_path_charpoly_derivative and polynomial extensionality therefore gives zero joinedVariation. The complete joined recovery theorem, with squared-edge variations 2*b*db, recovers every edge and loop direction. The readout is injective and hence surjective between two real spaces of dimension n.")),
            Paragraph(Text("Now take an arbitrary real X satisfying entrywise A times X equal to zero and A X-transpose equal to X-transpose A. The matrix Y=U-transpose X-transpose U commutes with the diagonal spectral matrix. Distinct spectral entries force every off-diagonal entry of Y to vanish; symmetry of X is a consequence here and is never assumed. Entrywise annihilation gives trace(X-transpose T(v))=0 for every support tangent. Choose v whose spectral diagonal readout equals diag(Y). Invariance of trace under the orthogonal change of basis identifies that trace with the sum of the squares of the diagonal entries of Y. Thus Y=0 and X=0. This argument tests the full unrestricted real commutant.")),
            Paragraph(Text("The companion KoljancicOblakEvenPathNSSP.result consumes these relations in a proof of the full claim. It applies the original Jacobi simple-spectrum supplier, takes square roots of the positive branch parameters, proves singleton-loop exact support and enlarges to every nonempty loop set using openness of the injective nSSP test map. Empty branches, endpoints and order two are included. The source Superpattern Lemma also preserves similarity, which is stronger than this existential event requires.")),
            Paragraph(Text("Source attribution and license boundaries are recorded in Library/Eigenstructure/koljancic2026nssp.md. The continuant variation argument is a repository derivation; the source question and its published definitions are not claimed as new results.")))));

    private static DocumentBlock Node(string id, string title, string name, DescribeRole role, string prose,
        bool literature = false, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("koljancic-even-path-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula ?? Definition(name))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Definition(string name)
    {
        Formula n = V("n"), k = V("k"), q = V("q"), dq = V("dq");
        Formula i = V("i"), j = V("j"), l = V("L"), a = V("A"), x = V("X");
        Formula fin = Call("Fin", n), reals = Seq(Operatorname, Grp(V("Real")));
        Formula matrix = Call("Matrix", fin, fin, reals);
        Formula succ = Add(k, D(1)), next = Add(k, D(2));
        Formula spectral = V("X");
        Formula P(Formula m) => Call(name, q, m);
        Formula Vary(Formula m) => Call(name, q, dq, m);
        Formula recurrence = All("q", Sequence(), And(Eq(P(D(0)), D(1)),
            And(Eq(P(D(1)), spectral), All("k", Nat(),
                Eq(P(next), Sub(Mul(spectral, P(succ)), Mul(Call("C", App(q, k)), P(k))))))));
        if (name == "continuant") return recurrence;
        if (name == "variation") return All("q", Sequence(), All("dq", Sequence(),
            And(Eq(Vary(D(0)), D(0)), And(Eq(Vary(D(1)), D(0)), All("k", Nat(),
                Eq(Vary(next), Sub(Sub(Mul(spectral, Vary(succ)),
                    Mul(Call("C", App(dq, k)), Call("continuant", q, k))),
                    Mul(Call("C", App(q, k)), Vary(k)))))))));
        if (name == "deformedContinuant") return All("q", Sequence(), All("dq", Sequence(),
            And(Eq(Vary(D(0)), D(1)), And(Eq(Vary(D(1)), Call("C", spectral)), All("k", Nat(),
                Eq(Vary(next), Sub(Mul(Call("C", spectral), Vary(succ)),
                    Mul(Add(Call("C", Call("C", App(q, k))),
                        Mul(Call("C", Call("C", App(dq, k))), V("z"))), Vary(k)))))))));
        if (name == "pathPattern") return All("n", Nat(), All("L", Call("Finset", fin),
            All("i", fin, All("j", fin, Iff(Call(name, l, i, j),
                Or(Eq(Add(Call("val", i), D(1)), Call("val", j)),
                    Or(Eq(Add(Call("val", j), D(1)), Call("val", i)),
                        And(Eq(i, j), new Formula.Relation(i, FormulaRelationOperator.MemberOf, l)))))))));
        if (name == "HasNSSP") return All("n", Nat(), All("A", matrix,
            Iff(Call(name, a), All("X", matrix,
                Imp(All("i", fin, All("j", fin, Eq(Mul(App(a, i, j), App(x, i, j)), D(0)))),
                    Imp(Eq(Sub(Mul(a, Call("transpose", x)), Mul(Call("transpose", x), a)), D(0)),
                        Eq(x, D(0))))))));
        if (name == "claim") return Iff(V("claim"), All("n", Nat(), Imp(Lt(D(0), n),
            Imp(Call("Even", n), All("L", Call("Finset", fin), Imp(Call("Nonempty", l),
                new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("A"), matrix,
                    And(All("i", fin, All("j", fin, Iff(Ne(App(a, i, j), D(0)),
                        Call("pathPattern", l, i, j)))), Call("HasNSSP", a)))))))));
        if (name == "weightedPath")
        {
            Formula b = V("b");
            Formula entry = If(Eq(Add(Call("val", i), D(1)), Call("val", j)),
                App(b, Sub(Sub(n, D(2)), Call("val", i))),
                If(Eq(Add(Call("val", j), D(1)), Call("val", i)),
                    App(b, Sub(Sub(n, D(2)), Call("val", j))), D(0)));
            return All("b", Sequence(), All("n", Nat(), All("i", fin, All("j", fin,
                Eq(App(Call(name, b, n), i, j), entry)))));
        }
        throw new System.ArgumentException("Unknown definition", nameof(name));
    }

    private static Formula Linearization()
    {
        Formula q = V("q"), dq = V("dq"), n = V("n");
        Formula p = Call("deformedContinuant", q, dq, n);
        return All("q", Sequence(), All("dq", Sequence(), All("n", Nat(),
            And(Eq(Call("coeff", p, D(0)), Call("continuant", q, n)),
                Eq(Call("coeff", p, D(1)), Call("variation", q, dq, n))))));
    }

    private static Formula Recovery()
    {
        Formula q = V("q"), dq = V("dq"), n = V("n"), k = V("k");
        Formula nonzero = All("k", Nat(), Imp(Lt(k, n), Ne(App(q, k), D(0))));
        Formula recovered = All("k", Nat(), Imp(Lt(k, n), Eq(App(dq, k), D(0))));
        return All("q", Sequence(), All("dq", Sequence(), All("n", Nat(), Imp(nonzero,
            Imp(Eq(Call("variation", q, dq, n), D(0)),
                Imp(Eq(Call("variation", q, dq, Add(n, D(1))), D(0)), recovered))))));
    }

    private static Formula Characteristic()
    {
        Formula b = V("b"), n = V("n"), k = V("k");
        Formula squares = Seq(LambdaLower, Sp, k, Colon, Sp, Nat(), Sp, Mapsto, Sp,
            new Formula.Power(App(b, k), D(2)));
        return All("b", Sequence(), All("n", Nat(),
            Eq(Call("charpoly", Call("weightedPath", b, n)), Call("continuant", squares, n))));
    }

    private static Formula JoinedMatrixBinders(Formula body)
    {
        Formula real = Seq(Operatorname, Grp(V("Real")));
        return All("bL", Sequence(), All("bR", Sequence(), All("a", real,
            All("r", Nat(), All("s", Nat(), body)))));
    }

    private static Formula JoinedMatrixDefinition()
    {
        Formula bl = V("bL"), br = V("bR"), a = V("a"), r = V("r"), s = V("s");
        Formula i = V("i"), j = V("j"), iv = Call("val", i), jv = Call("val", j);
        Formula weight(Formula v) => If(Lt(v, r), App(bl, v),
            App(br, Sub(Sub(Add(s, r), D(1)), v)));
        Formula entry = If(Eq(i, j), If(Eq(iv, r), a, D(0)),
            If(Eq(Add(iv, D(1)), jv), weight(iv),
                If(Eq(Add(jv, D(1)), iv), weight(jv), D(0))));
        Formula fin = Call("Fin", Add(Add(s, D(1)), r));
        return JoinedMatrixBinders(All("i", fin, All("j", fin,
            Eq(App(Call("joinedPath", bl, br, a, r, s), i, j), entry))));
    }

    private static Formula JoinedMatrixCharacteristic()
    {
        Formula bl = V("bL"), br = V("bR"), a = V("a"), r = V("r"), s = V("s"), k = V("k");
        Formula square(Formula b) => Seq(LambdaLower, Sp, k, Colon, Sp, Nat(), Sp, Mapsto, Sp,
            new Formula.Power(App(b, k), D(2)));
        Formula P(Formula b, Formula n) => Call("continuant", square(b), n);
        Formula expr = Sub(Add(Mul(P(bl, Add(r, D(1))), P(br, s)),
            Mul(P(bl, r), P(br, Add(s, D(1))))),
            Mul(Mul(Add(V("X"), Call("C", a)), P(bl, r)), P(br, s)));
        return JoinedMatrixBinders(Eq(Call("charpoly", Call("joinedPath", bl, br, a, r, s)), expr));
    }

    private static Formula JoinedMatrixDerivative()
    {
        Formula bl = V("bL"), br = V("bR"), dl = V("dbL"), dr = V("dbR");
        Formula a = V("a"), da = V("da"), r = V("r"), s = V("s"), x = V("x");
        Formula k = V("k"), t = V("t"), real = Seq(Operatorname, Grp(V("Real")));
        Formula lambda(string name, Formula type, Formula body) =>
            Seq(LambdaLower, Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body);
        Formula square(Formula b) => lambda("k", Nat(), new Formula.Power(App(b, k), D(2)));
        Formula delta(Formula b, Formula d) => lambda("k", Nat(), Mul(Mul(D(2), App(b, k)), App(d, k)));
        Formula perturb(Formula b, Formula d) => lambda("k", Nat(), Add(App(b, k), Mul(t, App(d, k))));
        Formula matrix = Call("joinedPath", perturb(bl, dl), perturb(br, dr), Add(a, Mul(t, da)), r, s);
        Formula function = lambda("t", real, Call("eval", x, Call("charpoly", matrix)));
        Formula derivative = Call("eval", x, Call("joinedVariation", square(bl), square(br),
            delta(bl, dl), delta(br, dr), a, da, r, s));
        Formula body = Call("HasDerivAt", function, derivative, D(0));
        return All("bL", Sequence(), All("bR", Sequence(), All("dbL", Sequence(), All("dbR", Sequence(),
            All("a", real, All("da", real, All("r", Nat(), All("s", Nat(), All("x", real, body)))))))));
    }

    private static Formula JoinedDefinition()
    {
        Formula ql = V("qL"), qr = V("qR"), dl = V("dqL"), dr = V("dqR");
        Formula a = V("a"), da = V("da"), r = V("r"), s = V("s"), x = V("X");
        Formula P(Formula q, Formula n) => Call("continuant", q, n);
        Formula Dp(Formula q, Formula d, Formula n) => Call("variation", q, d, n);
        Formula u = P(ql, r), v = P(qr, s), du = Dp(ql, dl, r), dv = Dp(qr, dr, s);
        Formula f = Sub(Mul(x, u), P(ql, Add(r, D(1))));
        Formula g = Sub(Mul(x, v), P(qr, Add(s, D(1))));
        Formula df = Sub(Mul(x, du), Dp(ql, dl, Add(r, D(1))));
        Formula dg = Sub(Mul(x, dv), Dp(qr, dr, Add(s, D(1))));
        Formula expr = Add(Sub(D(0), Mul(Mul(Call("C", da), u), v)),
            Mul(Sub(x, Call("C", a)), Add(Mul(du, v), Mul(u, dv))));
        expr = Sub(Sub(Sub(Sub(expr, Mul(df, v)), Mul(f, dv)), Mul(du, g)), Mul(u, dg));
        return JoinedBinders(Eq(Call("joinedVariation", ql, qr, dl, dr, a, da, r, s), expr));
    }

    private static Formula JoinedRecovery()
    {
        Formula ql = V("qL"), qr = V("qR"), dl = V("dqL"), dr = V("dqR");
        Formula a = V("a"), da = V("da"), r = V("r"), s = V("s"), k = V("k");
        Formula Nonzero(Formula q, Formula n) =>
            All("k", Nat(), Imp(Lt(k, n), Ne(App(q, k), D(0))));
        Formula Zero(Formula d, Formula n) =>
            All("k", Nat(), Imp(Lt(k, n), Eq(App(d, k), D(0))));
        Formula result = And(Eq(da, D(0)), And(Zero(dl, r), Zero(dr, s)));
        Formula body = Imp(Ne(a, D(0)), Imp(Call("Odd", Add(r, s)),
            Imp(Nonzero(ql, r), Imp(Nonzero(qr, s),
                Imp(Call("IsCoprime", Call("continuant", ql, r), Call("continuant", qr, s)),
                    Imp(Eq(Call("coeff", Call("deformedJoinedContinuant", ql, qr, dl, dr, a, da, r, s), D(1)), D(0)), result))))));
        return JoinedBinders(body);
    }

    private static Formula JoinedDeformation()
    {
        Formula ql = V("qL"), qr = V("qR"), dl = V("dqL"), dr = V("dqR");
        Formula a = V("a"), da = V("da"), r = V("r"), s = V("s");
        Formula x = Call("C", V("X")), z = V("z");
        Formula P(Formula q, Formula d, Formula n) => Call("deformedContinuant", q, d, n);
        Formula u = P(ql, dl, r), v = P(qr, dr, s);
        Formula loop = Add(Call("C", Call("C", a)), Mul(Call("C", Call("C", da)), z));
        Formula expr = Sub(Sub(Mul(Mul(Sub(x, loop), u), v),
            Mul(Sub(Mul(x, u), P(ql, dl, Add(r, D(1)))), v)),
            Mul(u, Sub(Mul(x, v), P(qr, dr, Add(s, D(1))))));
        return JoinedBinders(Eq(Call("deformedJoinedContinuant", ql, qr, dl, dr, a, da, r, s), expr));
    }

    private static Formula JoinedBinders(Formula body)
    {
        Formula real = Seq(Operatorname, Grp(V("Real")));
        body = All("s", Nat(), body);
        body = All("r", Nat(), body);
        body = All("da", real, body);
        body = All("a", real, body);
        body = All("dqR", Sequence(), body);
        body = All("dqL", Sequence(), body);
        body = All("qR", Sequence(), body);
        return All("qL", Sequence(), body);
    }

    private static Formula CoprimeBranches()
    {
        Formula r = V("r"), s = V("s"), ql = V("qL"), qr = V("qR"), k = V("k");
        Formula positive(Formula q) => All("k", Nat(), Lt(D(0), App(q, k)));
        Formula body = And(positive(ql), And(positive(qr),
            Call("IsCoprime", Call("continuant", ql, r), Call("continuant", qr, s))));
        body = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("qR"), Sequence(), body);
        body = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("qL"), Sequence(), body);
        return All("r", Nat(), All("s", Nat(), Imp(Call("Odd", Add(r, s)), body)));
    }

    private static Formula NsspBridge()
    {
        Formula bl = V("bL"), br = V("bR"), a = V("a"), r = V("r"), s = V("s");
        Formula u = V("U"), lam = V("lam"), k = V("k");
        Formula real = Seq(Operatorname, Grp(V("Real")));
        Formula fin = Call("Fin", Add(Add(s, D(1)), r));
        Formula matrix = Call("Matrix", fin, fin, real);
        Formula finiteSequence = new Formula.TypeArrow(fin, real);
        Formula square(Formula b) => Seq(LambdaLower, Sp, k, Colon, Sp, Nat(), Sp, Mapsto, Sp,
            new Formula.Power(App(b, k), D(2)));
        Formula nonzero(Formula b, Formula n) => All("k", Nat(), Imp(Lt(k, n), Ne(App(b, k), D(0))));
        Formula path = Call("joinedPath", bl, br, a, r, s), tr = Call("transpose", u);
        Formula body = Imp(Eq(Mul(tr, u), D(1)), Imp(Eq(Mul(u, tr), D(1)),
            Imp(Eq(Mul(Mul(tr, path), u), Call("diagonal", lam)),
                Imp(Call("Injective", lam), Call("HasNSSP", path)))));
        body = All("U", matrix, All("lam", finiteSequence, body));
        body = Imp(Call("IsCoprime", Call("continuant", square(bl), r),
            Call("continuant", square(br), s)), body);
        body = Imp(nonzero(br, s), body);
        body = Imp(nonzero(bl, r), body);
        body = Imp(Call("Odd", Add(r, s)), body);
        return JoinedMatrixBinders(Imp(Ne(a, D(0)), body));
    }

    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) =>
        a.Length == 0 ? Seq(Operatorname, Grp(V(s))) : App(Seq(Operatorname, Grp(V(s))), a);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [..a]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Nat() => Seq(Operatorname, Grp(V("Nat")));
    private static Formula Sequence() => new Formula.TypeArrow(Nat(), Seq(Operatorname, Grp(V("Real"))));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula If(Formula h, Formula a, Formula b) => Seq(Call("if"), Sp, Open, h, Close, Sp,
        Call("then"), Sp, a, Sp, Call("else"), Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
}
