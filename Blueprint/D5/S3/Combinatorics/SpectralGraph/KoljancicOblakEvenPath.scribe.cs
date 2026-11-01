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
                "This proposition is the full source question. No theorem in this module currently proves it.", true),
            Node("continuant", "Zero-diagonal branch continuant", "continuant", DescribeRole.Definition,
                "The empty branch has polynomial one and a one-vertex branch has polynomial X. Each successor step uses the squared weight of the newly attached edge."),
            Node("variation", "Edge-parameter first variation", "variation", DescribeRole.Definition,
                "The formal linearized recurrence includes the variation of the edge parameter and the variation of the preceding continuant. A connection to the actual characteristic-coefficient differential remains to be proved."),
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
            Paragraph(Text("The remaining whole-event bridges are the central-loop characteristic identity joining two weighted branches; a coprime choice for opposite-parity branches; separation of the complete central-vertex variation, retaining all product-rule cross terms; the coefficient/adjugate trace pairing and unrestricted real commutant argument; and exact support enlargement to every nonempty loop set. The source Superpattern Lemma also preserves similarity, which is stronger than the existential event requires.")),
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
