using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostChargeTensorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostChargeTensor.";
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
    private static Formula Smul(Formula x, Formula y) => C("smul", x, y);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("bc-ghost-charge-tensor-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(name.Replace("_", " ")), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Lam(string name, Formula type, Formula body) => Seq(LambdaLower, Open, V(name), Colon, type, Close, Mapsto, Open, body, Close);
    private static Formula Sum(Formula set, string name, Formula type, Formula body) => C("Finset.sum", set, Lam(name, type, body));
    private static Formula Matter(Formula body) => A("M", V("Type"), Seq(OpenBracket, C("AddCommGroup", V("M")), CloseBracket, Sp, OpenBracket, C("Module", V("Complex"), V("M")), CloseBracket, Sp, body));
    public DocumentDefinition Create()
    {
        var tensor = C("TensorProduct", V("Complex"), V("M"), V("Fock"));
        var end = C("Module.End", V("Complex"), tensor);
        var e = V("E"); var eps = V("epsilon"); var d = V("d"); var m = V("m"); var k = V("K"); var l = V("L"); var x = V("x");
        var n = V("number"); var ints = V("Int"); var modes = C("Finset", ints);
        var eb = Mul(e, C("B", m)); var be = Mul(C("B", m), e);
        var ec = Mul(e, C("C", m)); var ce = Mul(C("C", m), e);
        var commutator = Sub(Mul(n, e), Mul(e, n));
        var signed = Imp(Eqn(Mul(eps, eps), D(1)), Imp(A("m", ints, Eqn(eb, Smul(eps, be))), Imp(A("m", ints, Eqn(ec, Smul(eps, ce))), Eqn(commutator, D(0)))));
        var vanish = Imp(A("m", ints, Eqn(eb, be)), Imp(A("m", ints, Eqn(ec, ce)), A("d", V("Complex"), Imp(Ne(d, D(0)), Imp(Eqn(commutator, Smul(d, e)), Eqn(e, D(0)))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A nonzero ghost charge degree annihilates any endomorphism commuting with all tensor ghost modes.",
            H("Charged commutants with arbitrary matter"), Blocks(
                Paragraph(Text("M is an arbitrary complex module. Tensor products and endomorphisms are algebraic; no topology, finite dimension, positivity or irreducibility is assumed. The maps b, c and ghostNumber are the actual maps of BcGhostFock and BcGhostCharge. Bracketed group and module assumptions are anonymous instance arguments.")),
                Node("liftGhost", Matter(A("T", C("Module.End", V("Complex"), V("Fock")), Eqn(C("liftGhost", V("T")), C("TensorProduct.map", C("LinearMap.id", V("M")), V("T"))))), "The matter factor is acted on by its identity map.", DescribeRole.Definition),
                Node("number", Matter(Eqn(n, C("liftGhost", V("ghostNumber")))), "The tensor ghost-number operator.", DescribeRole.Definition),
                Node("B", Matter(A("m", ints, Eqn(C("B", m), C("liftGhost", C("b", m))))), "Every integer b mode acts on the ghost factor.", DescribeRole.Definition),
                Node("C", Matter(A("m", ints, Eqn(C("C", m), C("liftGhost", C("c", m))))), "Every integer c mode acts on the ghost factor.", DescribeRole.Definition),
                Node("partialNumber", Matter(A("K", modes, Eqn(C("partialNumber", k), Sum(k, "n", ints, C("liftGhost", C("normalTerm", V("n"))))))), "A finite sum of the actual lifted normal bilinears.", DescribeRole.Definition),
                Node("tensor_finite_capture", Matter(A("x", tensor, E("K", modes, A("L", modes, Imp(C("Finset.Subset", k, l), Eqn(C("partialNumber", l, x), C("number", x))))))), "Each pure tensor inherits a finite capture from its ghost vector. Tensor-product induction combines captures by finite union, so every larger finite set still computes number on the original tensor."),
                Node("number_commutes_of_signed_modes", Matter(A("E", end, A("epsilon", V("Complex"), signed))), "For epsilon squared equal to one, the two signs cancel in each normal bilinear. At a fixed x choose one finite union capturing x and E x. Commutation with that finite sum identifies number applied to E x with E applied to number x. Epsilon one gives commutation, and epsilon minus one covers anticommutation with both odd families."),
                Node("charged_commutant_vanishes", Matter(A("E", end, vanish)), "Finite normal capture first proves that the charge commutator is zero. The stipulated degree d is nonzero, so d times E equal to zero forces E itself to be zero. This uses no scalar-commutant assertion on the tensor product."),
                Paragraph(Text("The theorem can eliminate a later BRST residual only after that residual is constructed on this tensor carrier and its mode commutation and nonzero degree are proved. It does not construct a total BRST operator, prove nilpotence, or complete the string objective.")))));
    }
}
