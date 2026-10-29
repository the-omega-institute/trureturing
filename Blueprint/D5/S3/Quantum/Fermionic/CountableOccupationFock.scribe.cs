using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class CountableOccupationFockDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/CountableOccupationFock.";
    private static Formula V(string x) => F.Id(x);
    private static Formula C(string name, params Formula[] args)
    {
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count != 0) tokens.Add(Dot);
            tokens.Add(Operatorname); tokens.Add(Grp(F.Id(part)));
        }
        var fn = Seq(tokens.ToArray());
        return args.Length == 0 ? fn : new Formula.Apply(fn, [.. args]);
    }
    private static Formula A(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula E(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula SumAt(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(V(name), Colon, type)), Sp, body);
    private static Formula R(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Eqn(Formula x, Formula y) => R(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Lam(string x, Formula type, Formula body) => Seq(LambdaLower, Sp, Open, V(x), Colon, type, Close, Sp, Mapsto, Sp, body);
    private static Formula Nat => V("Nat");
    private static Formula Complex => V("Complex");
    private static Formula Sets => C("Finset", Nat);
    private static Formula Fock => V("Fock");
    private static Formula Assignment(Formula n) => C("Assignment", n);
    private static Formula Vector(Formula n) => new Formula.TypeArrow(Assignment(n), Complex);
    private static Formula End => C("Module.End", Complex, Fock);
    private static Formula Smul(Formula x, Formula y) => C("smul", x, y);
    private static Formula Ket(Formula s) => C("ket", s);
    private static Formula Emb(Formula n, Formula v) => C("prefixEmbed", n, v);
    private static Formula Act(string op, Formula j, Formula v) => C(op, j, v);
    private static Formula Mode(Formula j, Formula b) => C("mode", j, b);
    private static Formula BitPair => C("Prod", Nat, V("Bool"));
    private static Formula FinPair(Formula n) => C("Prod", C("Fin", n), V("Bool"));
    private static Formula Phase(Formula j, Formula s) => C("phase", j, s);
    private static Formula Member(Formula j, Formula s) => R(j, FormulaRelationOperator.MemberOf, s);
    private static Formula Below(Formula n, Formula m) => R(n, FormulaRelationOperator.LessThanOrEqual, m);
    private static Formula One => Seq(Open, D(1), Colon, End, Close);
    private static Formula Zero => D(0);
    private static Formula NegOne => Seq(Open, Minus, D(1), Colon, Complex, Close);
    private static Formula Power(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Ite(Formula condition, Formula yes, Formula no) => C("ite", condition, yes, no);
    private static Formula ScalarRule(bool creation)
    {
        var j = V("j"); var s = V("S");
        var nonzero = Smul(Phase(j, s), Ket(creation ? C("insert", j, s) : C("Finset.erase", s, j)));
        var body = Ite(Member(j, s), creation ? Zero : nonzero, creation ? nonzero : Zero);
        return A("j", Nat, Eqn(C(creation ? "create" : "annihilate", j),
            C("Finsupp.lsum", Complex, Lam("S", Sets, C("LinearMap.smulRight", C("LinearMap.id"), body)))));
    }
    private static Formula Bridge(bool creation)
    {
        var n = V("N"); var j = V("j"); var v = V("v");
        var matrix = C("fullC", j);
        if (creation) matrix = C("Matrix.conjTranspose", matrix);
        return A("N", Nat, A("j", C("Fin", n), A("v", Vector(n),
            Eqn(Act(creation ? "create" : "annihilate", C("Fin.val", j), Emb(n, v)), Emb(n, C("Matrix.mulVec", matrix, v))))));
    }
    private static Formula Coherence(bool? creation)
    {
        var n = V("N"); var m = V("M"); var v = V("v"); var j = V("j");
        var ext = C("prefixExtend", n, m, v);
        Formula statement;
        if (creation is null) statement = Eqn(Emb(m, ext), Emb(n, v));
        else
        {
            var left = C("fullC", C("Fin.castLE", V("h"), j)); var right = C("fullC", j);
            if (creation is true) { left = C("Matrix.conjTranspose", left); right = C("Matrix.conjTranspose", right); }
            statement = Eqn(C("Matrix.mulVec", left, ext), C("prefixExtend", n, m, C("Matrix.mulVec", right, v)));
        }
        var body = A("v", Vector(n), statement);
        if (creation is not null) body = A("j", C("Fin", n), body);
        return A("N", Nat, A("M", Nat, creation is null ? Imp(Below(n, m), body) : A("h", Below(n, m), body)));
    }
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("countable-occupation-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(name.Replace("_", " ")), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create()
    {
        var n = V("N"); var m = V("M"); var j = V("j"); var i = V("i"); var s = V("S"); var v = V("v"); var b = V("b");
        var p = V("p"); var w = V("w");
        var map = C("List.map", Lam("p", FinPair(n), C("Prod.mk", C("Fin.val", C("Prod.fst", p)), C("Prod.snd", p))), w);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Countably many fermionic modes act on all finite occupation states through an exact coherent finite-prefix construction.",
            H("Countable finite-excitation Fock space"), Blocks(
                Paragraph(Text("The carrier is algebraic: every state has finite support among finite subsets of the natural numbers. No completion or infinite operator sum is used. FullC is the original finite Jordan–Wigner annihilator. Its signed entry formula is supplied by HardCoreCompression.fullC_entry; the Boolean occupation encoding and its inverse are supplied by CompletedCorrelationalBound. The new intertwinings identify those matrix actions with the all-particle-number signed occupation action. Finite capture and word transport then transfer the actual finite CAR to unrestricted natural indices. The same-site square is obtained algebraically from FockMajoranaCarrier.majorana_clifford_and_parity. The linear extension uses Mathlib Finsupp.lsum.")),
                Node("Fock", Eqn(Fock, C("Finsupp", Sets, Complex)), "The direct sum has one coordinate for each finite occupation set.", DescribeRole.Definition),
                Node("ket", A("S", Sets, Eqn(Ket(s), C("Finsupp.single", s, D(1)))), "The occupation basis vector has coefficient one at S.", DescribeRole.Definition),
                Node("vacuum", Eqn(V("vacuum"), Ket(C("Finset.empty"))), "The vacuum is the empty occupation.", DescribeRole.Definition),
                Node("lowerCount", A("j", Nat, A("S", Sets, Eqn(C("lowerCount", j, s), C("Finset.card", C("Finset.filter", Lam("i", Nat, R(i, FormulaRelationOperator.LessThan, j)), s))))), "Only occupied sites strictly below j contribute to the sign.", DescribeRole.Definition),
                Node("phase", A("j", Nat, A("S", Sets, Eqn(Phase(j, s), Power(NegOne, C("lowerCount", j, s))))), "The sign is real and equals plus or minus one.", DescribeRole.Definition),
                Node("annihilate", ScalarRule(false), "The signed deletion rule extends linearly to a genuine endomorphism.", DescribeRole.Definition),
                Node("create", ScalarRule(true), "The signed insertion rule vanishes at an already occupied site and extends linearly.", DescribeRole.Definition),
                Node("parity", Eqn(V("parity"), C("Finsupp.lsum", Complex, Lam("S", Sets, C("LinearMap.smulRight", C("LinearMap.id"), Smul(Power(NegOne, C("Finset.card", s)), Ket(s)))))), "Parity is the occupation-cardinality sign.", DescribeRole.Definition),
                Node("prefixEmbed", A("N", Nat, A("v", Vector(n), Eqn(Emb(n, v), SumAt("t", Assignment(n), Smul(C("v", V("t")), Ket(C("occupationSet", V("t")))))))), "The finite Boolean vector is embedded by its original occupation coordinates.", DescribeRole.Definition),
                Node("prefixEmbed_injective", A("N", Nat, C("Function.Injective", C("prefixEmbed", n))), "Reading the coefficient at an encoded occupation recovers the finite input coordinate."),
                Node("jw_annihilate_intertwining", Bridge(false), "The existing signed matrix coefficient and occupation deletion identify the two actual actions."),
                Node("jw_create_intertwining", Bridge(true), "Conjugate transposition of the existing entry formula gives signed occupation insertion; the phase is real."),
                Node("prefixExtend", A("N", Nat, A("M", Nat, A("v", Vector(n), Eqn(C("prefixExtend", n, m, v), SumAt("t", Assignment(n), Smul(C("v", V("t")), C("Pi.single", C("occupationOfSet", m, C("occupationSet", V("t"))), D(1)))))))), "Assignments are extended by false at the additional sites. On basis assignments the displayed occupationOfSet formula is literal.", DescribeRole.Definition),
                Node("prefix_coherence", Coherence(null), "For N at most M, extending by empty sites preserves the countable state."),
                Node("cutoff_annihilate_coherence", Coherence(false), "Injectivity of the larger embedding and the annihilator intertwining prove coherent matrix transport."),
                Node("cutoff_create_coherence", Coherence(true), "The creator matrices obey the same coherent extension law."),
                Node("finite_capture", A("v", Fock, A("J", Sets, E("N", Nat, And(A("j", Nat, Imp(Member(j, V("J")), R(j, FormulaRelationOperator.LessThan, n))), E("w", Vector(n), Eqn(Emb(n, w), v)))))), "One prefix contains every occupied site of the state and every site in the selected finite set J. Capture is exact, including the empty-state boundary."),
                Node("mode", A("j", Nat, A("b", V("Bool"), Eqn(Mode(j, b), Ite(b, C("create", j), C("annihilate", j))))), "True selects creation and false selects annihilation.", DescribeRole.Definition),
                Node("finiteMode", A("N", Nat, A("j", C("Fin", n), A("b", V("Bool"), Eqn(C("finiteMode", j, b), Ite(b, C("Matrix.conjTranspose", C("fullC", j)), C("fullC", j)))))), "The finite supplier follows the same Boolean convention.", DescribeRole.Definition),
                Node("word", And(Eqn(C("word", C("List.nil")), One), A("p", BitPair, A("w", C("List", BitPair), Eqn(C("word", C("List.cons", p, w)), Mul(Mode(C("Prod.fst", p), C("Prod.snd", p)), C("word", w)))))), "Products act on the rightmost state first.", DescribeRole.Definition),
                Node("finiteWord", A("N", Nat, And(Eqn(C("finiteWord", C("List.nil")), C("Matrix.one", Assignment(n))), A("p", FinPair(n), A("w", C("List", FinPair(n)), Eqn(C("finiteWord", C("List.cons", p, w)), Mul(C("finiteMode", C("Prod.fst", p), C("Prod.snd", p)), C("finiteWord", w))))))), "Finite matrix words include the empty identity word.", DescribeRole.Definition),
                Node("word_intertwining", A("N", Nat, A("w", C("List", FinPair(n)), A("v", Vector(n), Eqn(C("word", map, Emb(n, v)), Emb(n, C("Matrix.mulVec", C("finiteWord", w), v)))))), "Both single-operator intertwinings propagate through every finite word."),
                Node("car", A("i", Nat, A("j", Nat, A("a", V("Bool"), A("b", V("Bool"), Eqn(Add(Mul(Mode(i, V("a")), Mode(j, b)), Mul(Mode(j, b), Mode(i, V("a")))), Ite(And(Eqn(i, j), R(V("a"), FormulaRelationOperator.NotEqual, b)), One, Zero)))))), "Every finite state and the two chosen indices fit in one prefix. Word transport consumes the finite CAR, including the equal-site nilpotence supplied by the Majorana relations."),
                Node("annihilate_vacuum", A("j", Nat, Eqn(Act("annihilate", j, V("vacuum")), Zero)), "No site is occupied in the vacuum."),
                Node("create_vacuum", A("j", Nat, Eqn(Act("create", j, V("vacuum")), Ket(C("Finset.singleton", j)))), "Insertion into the vacuum has sign one."),
                Node("parity_involution", Eqn(Mul(V("parity"), V("parity")), One), "Squaring the occupation sign gives the identity on every basis state."),
                Node("parity_odd", A("j", Nat, A("b", V("Bool"), Eqn(Add(Mul(V("parity"), Mode(j, b)), Mul(Mode(j, b), V("parity"))), Zero))), "Every nonzero insertion or deletion changes the cardinality by one."),
                Node("creator_spanning", Eqn(C("Submodule.span", Complex, C("Set.range", Lam("w", C("List", Nat), C("word", C("List.map", Lam("j", Nat, C("Prod.mk", j, V("true"))), w), V("vacuum"))))), C("Submodule.top", Complex, Fock)), "Insertion induction produces each occupation basis vector as a nonzero scalar multiple of a creator word. Finite linear extension spans the entire carrier."),
                Node("common_annihilator_kernel", A("v", Fock, Iff(A("j", Nat, Eqn(Act("annihilate", j, v), Zero)), E("alpha", Complex, Eqn(v, Smul(V("alpha"), V("vacuum")))))), "If a nonempty occupation S contains j, the coefficient of S with j deleted in annihilate j v is phase j S times the coefficient of S in v. Deletion is injective among occupations containing j, and the sign is nonzero. Thus every nonempty coefficient vanishes, while the empty coefficient supplies the unique scalar. Conversely all annihilators kill each scalar multiple of the actual vacuum."),
                Node("eq_scalar_of_creator_commutation", A("A", End, A("alpha", Complex, Imp(Eqn(new Formula.Apply(V("A"), [V("vacuum")]), Smul(V("alpha"), V("vacuum"))), Imp(A("j", Nat, Eqn(Mul(V("A"), C("create", j)), Mul(C("create", j), V("A")))), Eqn(V("A"), Smul(V("alpha"), One)))))), "Commutation moves A through each finite creator word. Its scalar action on the vacuum therefore holds on every creator-word state, and creator_spanning with linear-map extensionality extends that same scalar to every Fock vector. No irreducibility hypothesis or finite cutoff is imposed."),
                Paragraph(Text("This algebraic representation asserts CAR, exact cutoff transport and parity. Statewise quadratic normal sums, the bc Virasoro anomaly, the all-state super vertex algebra, graded tensor matter, BRST charge and nilpotence, cohomology, no-ghost results and the Monster, sewing, string and AdS identifications require further constructions.")))));
    }
}
