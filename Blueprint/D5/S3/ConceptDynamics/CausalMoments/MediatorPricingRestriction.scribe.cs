using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class MediatorPricingRestrictionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original causal pricing is preserved exactly under finite response-coordinate restriction.", H("MediatorPricingRestriction"), Blocks(
            Paragraph(Text("M is finite with decidable equality. coupling is the existing normalized rational law on M times M; K is a Finset M; branch maps the subtype K to Bool; table and color map M to Bool; multiplier maps M to Q. All sums are over the whole M carrier.")),
            Describe.Lean(DescribeId.Create("pin-table"), DeclarationHandle.Create(Prefix + "pinTable"),
                H("Extend the selected response assignment"), StatementSource.FromAuthor(Disp(All("M K branch i", B(C("pinTable" , V("K"), V("branch"), V("i")), Eq, C("ite" , B(V("i"), InMacro, V("K")), C("branch" , V("i")), V("false")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The branch is defined on the finite subtype K. The application branch(i) on membership uses the corresponding subtype witness; all other coordinates are false."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("clamp-table"), DeclarationHandle.Create(Prefix + "clampTable"),
                H("Reassemble an original response column"), StatementSource.FromAuthor(Disp(All("M K branch table i", B(C("clampTable" , V("K"), V("branch"), V("table"), V("i")), Eq, C("ite" , B(V("i"), InMacro, V("K")), C("apply" , C("pinTable" , V("K"), V("branch")), V("i")), C("table" , V("i"))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fixed coordinates use the selected branch and all free coordinates retain the supplied original table values."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("clamp-table-restrict"), DeclarationHandle.Create(Prefix + "clampTable_restrict"),
                H("Every original column has a branch"), StatementSource.FromAuthor(Disp(All("M K table", B(C("clampTable" , V("K"), Lam("i", C("table" , V("i"))), V("table")), Eq, V("table"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here i in the restriction lambda ranges over K, with its underlying mediator value used by table. No original complete table is excluded."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("absorb-pair"), DeclarationHandle.Create(Prefix + "absorbPair"),
                H("Redirect removed mass to the diagonal"), StatementSource.FromAuthor(Disp(All("M K pair", B(C("absorbPair" , V("K"), V("pair")), Eq, C("ite" , And(C("not" , B(C("fst" , V("pair")), InMacro, V("K"))), C("not" , B(C("snd" , V("pair")), InMacro, V("K")))), V("pair"), C("pair" , C("fst" , V("pair")), C("fst" , V("pair")))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Free/free pairs are unchanged. All other pairs retain their mass on a diagonal pair. This is a computational map, not conditioning the mediator law."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("residual-coupling"), DeclarationHandle.Create(Prefix + "residualCoupling"),
                H("Keep the normalized response-law API"), StatementSource.FromAuthor(Disp(All("M coupling K", B(C("residualCoupling" , V("coupling"), V("K")), Eq, C("pushforwardResponseLaw" , V("coupling"), C("absorbPair" , V("K"))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The deterministic pushforward stays on the full mediator-pair carrier and preserves normalization and nonnegativity. Its changed marginal values are not substituted into the original data constraints."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("residual-coupling-off-diagonal"), DeclarationHandle.Create(Prefix + "residualCoupling_offDiagonal"),
                H("Compute the residual off-diagonal coefficients"), StatementSource.FromAuthor(Disp(All("M coupling K i j", B(B(V("i"), Neq, V("j")), Rightarrow, B(C("mass" , C("residualCoupling" , V("coupling"), V("K")), C("pair" , V("i"), V("j"))), Eq, C("ite" , And(C("not" , B(V("i"), InMacro, V("K"))), C("not" , B(V("j"), InMacro, V("K")))), C("mass" , V("coupling"), C("pair" , V("i"), V("j"))), Z)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Outside the diagonal, the residual keeps exactly the original coefficients with both endpoints free."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("residual-coupling-bipartite-iff"), DeclarationHandle.Create(Prefix + "residualCoupling_bipartite_iff"),
                H("Identify the exact graph condition"), StatementSource.FromAuthor(Disp(All("M coupling K color", B(C("OffDiagonalBipartite" , C("residualCoupling" , V("coupling"), V("K")), V("color")), Leftrightarrow, All("i j", B(And(C("not" , B(V("i"), InMacro, V("K"))), C("not" , B(V("j"), InMacro, V("K"))), B(V("i"), Neq, V("j")), B(C("mass" , V("coupling"), C("pair" , V("i"), V("j"))), Neq, Z)), Rightarrow, B(C("color" , V("i")), Neq, C("color" , V("j"))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bipartiteness concerns the original support after removing K, including both directed orientations. Original self-loops impose no condition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("branch-multiplier"), DeclarationHandle.Create(Prefix + "branchMultiplier"),
                H("Retain both oriented boundary contributions"), StatementSource.FromAuthor(Disp(All("M coupling K branch multiplier i", B(C("branchMultiplier" , V("coupling"), V("K"), V("branch"), V("multiplier"), V("i")), Eq, B(B(C("ite" , B(V("i"), InMacro, V("K")), Z, C("multiplier" , V("i"))), Plus, SumF("j", C("ite" , And(C("not" , B(V("i"), InMacro, V("K"))), B(V("j"), InMacro, V("K")), B(C("apply" , C("pinTable" , V("K"), V("branch")), V("j")), Eq, V("true"))), C("mass" , V("coupling"), C("pair" , V("i"), V("j"))), Z))), Minus, SumF("j", C("ite" , And(B(V("j"), InMacro, V("K")), C("not" , B(V("i"), InMacro, V("K"))), B(C("apply" , C("pinTable" , V("K"), V("branch")), V("j")), Eq, V("false"))), C("mass" , V("coupling"), C("pair" , V("j"), V("i"))), Z))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Free-to-fixed-one edges add to the multiplier; fixed-zero-to-free edges subtract. Fixed-coordinate multipliers become zero in the residual problem and stay in the branch offset."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("branch-offset"), DeclarationHandle.Create(Prefix + "branchOffset"),
                H("Compute the constant in the original objective"), StatementSource.FromAuthor(Disp(All("M coupling K branch multiplier", B(C("branchOffset" , V("coupling"), V("K"), V("branch"), V("multiplier")), Eq, C("completeMediatorPricingScore" , V("coupling"), V("multiplier"), C("pinTable" , V("K"), V("branch"))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The offset includes fixed/fixed benefit, free-zero/fixed-one benefit and all original fixed-coordinate multiplier contributions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pricing-restriction-identity"), DeclarationHandle.Create(Prefix + "pricing_restriction_identity"),
                H("Exact original-to-residual pricing equality"), StatementSource.FromAuthor(Disp(All("M coupling K branch multiplier table", B(C("completeMediatorPricingScore" , V("coupling"), V("multiplier"), C("clampTable" , V("K"), V("branch"), V("table"))), Eq, B(C("branchOffset" , V("coupling"), V("K"), V("branch"), V("multiplier")), Plus, C("completeMediatorPricingScore" , C("residualCoupling" , V("coupling"), V("K")), C("branchMultiplier" , V("coupling"), V("K"), V("branch"), V("multiplier")), V("table"))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This equality holds before any bipartite assumption. No removed mass is renormalized, and reassembly gives one actual original outcome-response table."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Z => F.D(0);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula B(Formula x, Formula op, Formula y) => Seq(P(x), Sp, op, Sp, P(y));
    private static Formula All(string names, Formula body) => Quantify(Forall, names, body);
    private static Formula Lam(string names, Formula body) => Quantify(LambdaLower, names, body);
    private static Formula SumF(string name, Formula body) => Seq(F.Sum, Underscore, Grp(V(name)), Sp, P(body));
    private static Formula Quantify(Formula q, string names, Formula body)
    {
        var items = new List<Formula> { q, Sp };
        foreach (var name in names.Split(' ')) items.AddRange([V(name), Comma, Sp]);
        items.Add(body); return Seq([.. items]);
    }
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var k = 0; k < clauses.Length; k++)
        {
            if (k > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(P(clauses[k]));
        }
        return Seq([.. items]);
    }
    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var k = 0; k < args.Length; k++)
        {
            if (k > 0) items.AddRange([Comma, Sp]);
            items.Add(args[k]);
        }
        items.Add(Close); return Seq([.. items]);
    }
}
