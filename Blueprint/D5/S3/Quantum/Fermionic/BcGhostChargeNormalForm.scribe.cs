using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostChargeNormalFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostChargeNormalForm.";

    private static Formula V(string x) => F.Id(x);
    private static Formula C(string name, params Formula[] args)
    {
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count != 0) tokens.Add(Dot);
            tokens.Add(Operatorname);
            tokens.Add(Grp(F.Id(part)));
        }
        var fn = Seq(tokens.ToArray());
        return args.Length == 0 ? fn : new Formula.Apply(fn, [.. args]);
    }

    private static Formula A(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Neg(Formula x) => new Formula.Negate(x);
    private static Formula Smul(Formula x, Formula y) => C("smul", x, y);
    private static Formula Ite(Formula condition, Formula yes, Formula no) =>
        C("ite", condition, yes, no);
    private static Formula Typed(Formula x, Formula type) => Seq(Open, x, Colon, type, Close);
    private static Formula Lam(Formula x, Formula body) =>
        Seq(Open, x, Mapsto, body, Close);
    private static Formula FinSum(Formula x, Formula type, Formula body) =>
        Seq(F.Sum, Underscore, Grp(x, InMacro, Sp, type), Caret, Grp(V("fin")), body);
    private static Formula Int => V("Int");
    private static Formula Fock => V("Fock");
    private static Formula End => C("Module.End", V("Complex"), Fock);
    private static Formula Half => Typed(C("div", D(1), D(2)), V("Complex"));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("bc-ghost-charge-normal-form-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name),
        H(name.Replace("_", " ")),
        StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))),
        role);

    public DocumentDefinition Create()
    {
        var n = V("n");
        var v = V("v");
        var bound = V("A");
        var orderedOnState = Lam(n, C("orderedTerm", n, v));
        var orderedOperator = Ite(Le(Neg(D(1)), n),
            Mul(C("c", Neg(n)), C("L", n)),
            Mul(C("L", n), C("c", Neg(n))));
        var orderedValue = Ite(Le(Neg(D(1)), n),
            C("c", Neg(n), C("L", n, v)),
            C("L", n, C("c", Neg(n), v)));

        var supportBound = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("A"), Int,
            new Formula.Logic(Le(D(0), bound), FormulaLogicOperator.And,
                new Formula.Relation(C("Function.support", orderedOnState),
                    FormulaRelationOperator.SubsetOf,
                    C("Set.Icc", Neg(bound), Mul(D(2), bound)))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The original cubic ghost charge has an all-state half-normal c/L expression.",
            H("The half-normal form of the original ghost charge"),
            Blocks(
                Paragraph(Text("This document describes the two public definitions and three public theorems of BcGhostChargeNormalForm. The carrier is the original CountableOccupationFock.Fock, the complex vector space of finitely supported functions on finite subsets of the natural numbers. Every state is an arbitrary finite complex linear combination of occupation kets, not just a vacuum, a chosen basis state or a truncated sector.")),
                Paragraph(Text("The operators are the existing BcGhostFock.b and c, BcGhostVirasoro.L and BcGhostBRST.Qg, with the original vacuum cuts b at minus one and c at two. L uses the original statewise finite Virasoro sum and Qg the original statewise finite ordered-pair cubic sum. The identity compares those operators directly; it neither introduces a replacement charge nor recreates a historical lattice namespace.")),
                Paragraph(Text("This is the classical algebraic bc ghost construction of weights two and minus one. See Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. Attribution retained from the mathematical source also includes Scott Carnahan's vertexAlg, Apache-2.0, revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, for the related field and normal-product constructions recorded in BcGhostStateField. The source credits the retained LatticeBcGhostBrstCharge.N/A source mechanism for its outer ordering and half coefficient, with retained source SHA256 c86ba73030f046ed86c83c5e4103a9970910a7b6c83eb1f76860c284b8ccd3a8; this is provenance, not a dependency imported by this module. No novelty of the ghost formulas is claimed.")),

                Node("orderedTerm",
                    A("n", Int, Eqn(Typed(C("orderedTerm", n), End), orderedOperator)),
                    "For every integer n this is an actual complex-linear endomorphism of the original Fock space. Multiplication of endomorphisms means composition, with the right factor acting first. The endpoint n = -1 is in the first branch: its value on v is c 1 (L (-1) v). There is no half coefficient in this term; that coefficient belongs outside the complete sum.",
                    DescribeRole.Definition),

                Node("orderedTerm_support",
                    A("v", Fock, supportBound),
                    "The complete assertion is that each input v has some nonnegative integer A bounding the support between -A and 2*A. In the proof, a basis occupation S uses A = S.sup id + 3. For n < -A the rightmost c (-n) kills ket S, and for n > 2*A the rightmost L n kills ket S. Finite linear combinations are handled by linear induction, using the maximum of the bounds for two summands. The bound depends on v; this asserts neither a global cutoff nor finite support of the endomorphism family itself."),

                Node("orderedTerm_finite",
                    A("v", Fock, C("Function.HasFiniteSupport", orderedOnState)),
                    "For every original state, the function n mapped to orderedTerm n v has finite support. The proof obtains this from containment in the finite integer interval of orderedTerm_support. This statewise fact is available before sum additivity and scalar compatibility are used; there is no analytic convergence or limiting prescription."),

                Node("halfNormalCharge",
                    A("v", Fock, Eqn(C("halfNormalCharge", v),
                        Smul(Half, FinSum(n, Int, C("orderedTerm", n, v))))),
                    "The definition has type Module.End Complex Fock, and this equation specifies its value on every v. Additivity uses orderedTerm_finite on both inputs before distributing the finite-support sum. Complex linearity likewise uses the actual finite support before moving a scalar through the sum. The scalar is exactly (1/2 : Complex), applied once to the entire sum.",
                    DescribeRole.Definition),

                Paragraph(Text("Joint support is needed in addition to finite support of the outer ordered family. The proof expands each L n using the original summand n q. Its private expandedTerm n q is c (-n) composed with summand n q in the n >= -1 branch, and summand n q composed with c (-n) otherwise. The four ordering cases in the private CAR calculation give expandedTerm n q = (2 : Complex) smul cubicTerm (-n,q). In the crossed cuts the mixed CAR contraction is zero, so this calculation introduces no boundary correction. The existing cubicTerm_finite v then gives finite support of the actual pair-indexed expansion (n,q) on every v, by the first-coordinate sign involution. These are statewise supports of the original operators.")),
                Paragraph(Text("Only after that joint support is established does the proof flatten the iterated sum over n and q into a sum over integer pairs. The expansion through c (-n) also uses summand_finite n v in its first branch; in the other branch the Virasoro sum is evaluated on the actual state c (-n) v. The sole pair reindexing is the bijection (n,q) mapped to (-n,q), identifying the pair sum with twice the original cubic charge. The exterior half cancels that factor two. The finite-support hypotheses justify this algebraic sum exchange without an analytic convergence assumption.")),

                Node("Qg_eq_halfNormalCharge",
                    A("v", Fock, Eqn(C("Qg", v), Smul(Half, FinSum(n, Int, orderedValue)))),
                    "The literal endpoint is Qg v = (1/2 : Complex) smul finsum (n : Int), if -1 <= n then c (-n) (L n v) else L n (c (-n) v). It quantifies over every original Fock state with no additional premise. In particular it assumes no lattice, rank, Gram form, criticality, nilpotence or cohomology condition. The proof first identifies Qg v with halfNormalCharge v and then unfolds the actual orderedTerm; the public theorem itself states the displayed sum, not just the name of the comparison operator."),

                Paragraph(Text("The exact scope is this algebraic ghost-sector operator identity and its statewise finite-support infrastructure. It supplies a connected prerequisite for further original-operator arguments. It does not establish the matter-tensor BRST construction, nilpotence, cohomology, a no-ghost theorem, a Borcherds identity, the Moonshine/VOA/CFT and anomaly/fusion programme, full string theory or AdS/CFT."))
            )));
    }
}
