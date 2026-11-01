using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostChargeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostCharge.";
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
    private static Formula Smul(Formula x, Formula y) => C("smul", x, y);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Negate(Formula x) => new Formula.Negate(x);
    private static Formula B(Formula m) => C("b", m);
    private static Formula G(Formula m) => C("c", m);
    private static Formula Omega => V("vacuum");
    private static Formula Zero => D(0);
    private static Formula Ite(Formula condition, Formula yes, Formula no) => C("ite", condition, yes, no);
    private static Formula NatPart(Formula x) => C("Int.toNat", x);
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("bc-ghost-charge-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(name.Replace("_", " ")), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Lam(string name, Formula type, Formula body) => Seq(LambdaLower, Open, V(name), Colon, type, Close, Mapsto, Open, body, Close);
    private static Formula Sum(Formula set, string name, Formula type, Formula body) => C("Finset.sum", set, Lam(name, type, body));
    private static Formula Cast(Formula x) => C("Int.cast", x);
    public DocumentDefinition Create()
    {
        var s = V("S"); var j = V("j"); var n = V("n"); var v = V("v"); var k = V("K");
        var nat = V("Nat"); var ints = V("Int"); var fock = V("Fock"); var sets = C("Finset", nat); var modes = C("Finset", ints);
        var even = Eqn(C("Nat.mod", j, D(2)), D(0)); var odd = Eqn(C("Nat.mod", j, D(2)), D(1));
        var q = C("charge", s); var number = V("ghostNumber");
        var normal = C("normalTerm", n); var site = C("modeSite", n);
        var partial = Sum(k, "n", ints, normal);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Signed ghost number is an actual diagonal operator and a pointwise finite normal-ordered sum.",
            H("Ghost number on countable occupation Fock space"), Blocks(
                Paragraph(Text("The carrier, vacuum, creators, annihilators and integer b and c modes are the original CountableOccupationFock and BcGhostFock objects. Charge counts odd occupied sites minus even occupied sites using integer subtraction. All casts in the operator formulas are into Complex. Products compose from right to left.")),
                Node("charge", A("S", sets, Eqn(q, Sub(C("Int.ofNat", C("Finset.card", C("Finset.filter", Lam("j", nat, odd), s))), C("Int.ofNat", C("Finset.card", C("Finset.filter", Lam("j", nat, even), s)))))), "The empty occupation has charge zero, an even singleton has charge minus one, and an odd singleton has charge plus one.", DescribeRole.Definition),
                Node("siteSign", A("j", nat, Eqn(C("siteSign", j), Ite(even, Negate(D(1)), D(1)))), "The signed contribution of one occupied site.", DescribeRole.Definition),
                Node("ghostNumber", A("S", sets, Eqn(C("ghostNumber", C("ket", s)), Smul(Cast(q), C("ket", s)))), "Finsupp.lsum extends this prescribed basis action complex linearly to every finite-excitation vector.", DescribeRole.Definition),
                Node("ghost_number_relations", And(Eqn(C("ghostNumber", Omega), Zero), And(A("m", ints, Eqn(Sub(Mul(number, B(V("m"))), Mul(B(V("m")), number)), Negate(B(V("m"))))), A("m", ints, Eqn(Sub(Mul(number, G(V("m"))), Mul(G(V("m")), number)), G(V("m")))))), "Insertion and deletion change the integer occupation charge by opposite site signs. Applying the four mode branches proves both degree identities for every integer, including the zero modes."),
                Node("siteTerm", A("j", nat, Eqn(C("siteTerm", j), Smul(Cast(C("siteSign", j)), Mul(C("create", j), C("annihilate", j))))), "The two Jordan–Wigner phases multiply to one on an occupied site; the bilinear vanishes on an empty site.", DescribeRole.Definition),
                Node("normalTerm", A("n", ints, Eqn(normal, Ite(Le(n, D(1)), Mul(G(n), B(Negate(n))), Negate(Mul(B(Negate(n)), G(n)))))), "Normal ordering uses the exact vacuum cuts at one and two.", DescribeRole.Definition),
                Node("modeSite", A("n", ints, Eqn(site, Ite(Le(n, D(1)), Add(Mul(D(2), NatPart(Sub(D(1), n))), D(1)), Mul(D(2), NatPart(Sub(n, D(2))))))), "This bijection labels odd sites by modes at most one and even sites by modes at least two.", DescribeRole.Definition),
                Node("siteMode", A("j", nat, Eqn(C("siteMode", j), Ite(even, Add(C("Int.ofNat", C("Nat.div", j, D(2))), D(2)), Sub(D(1), C("Int.ofNat", C("Nat.div", j, D(2))))))), "The inverse integer label of a natural occupation site.", DescribeRole.Definition),
                Node("activeModes", A("v", fock, Eqn(C("activeModes", v), C("Finset.image", V("siteMode"), C("Finset.biUnion", C("Finsupp.support", v), V("id"))))), "The union of the finite occupations in the support of this input supplies a finite set of integer labels.", DescribeRole.Definition),
                Node("finite_normal_capture", A("v", fock, A("K", modes, Imp(C("Finset.Subset", C("activeModes", v), k), Eqn(new Formula.Apply(partial, [v]), C("ghostNumber", v))))), "Every finite superset of the active labels computes the actual ghost number on this input. The proof uses the exact occupied-site projection and the bijection between sites and integer modes."),
                Node("normal_term_finite_support", A("v", fock, C("Function.HasFiniteSupport", Lam("n", ints, C("normalTerm", n, v)))) , "The support of the evaluated family is contained in activeModes v. This does not assert finite support of the endomorphism family."),
                Node("ghost_number_normal_sum", A("v", fock, Eqn(C("ghostNumber", v), C("finsum", Lam("n", ints, C("normalTerm", n, v))))), "The locally finite sum is formed separately at each input. No infinite endomorphism sum is assumed."),
                Paragraph(Text("These statements construct ghost number in the algebraic bc representation. They do not construct the total BRST operator, prove its square is zero, or establish a string or AdS/CFT theorem.")))));
    }
}
