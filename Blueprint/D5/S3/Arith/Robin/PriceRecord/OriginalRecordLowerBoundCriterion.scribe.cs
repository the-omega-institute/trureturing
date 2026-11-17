using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class OriginalRecordLowerBoundCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original strict integer-record one-sided normalized lower bounds characterize RH",
        H("An eventual lower-bound criterion on original records"),
        Blocks(Describe.Lean(DescribeId.Create("original-record-lower-bound-iff-rh"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/OriginalRecordLowerBoundCriterion.original_record_lower_bound_iff_rh"),
            H("The complete original-record criterion"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("D(x)=sqrt(x)*log(x). The objective is the existing "
                    + "goldenResourceObjective(lambda,n), and robinLogMargin and largestPrime "
                    + "are their original arithmetic definitions. A single pair of real constants "
                    + "M,T with T>=2 works for every natural m>=2, every real lambda>0, and "
                    + "strict objective dominance over EVERY positive n<m. The clock is the "
                    + "largest prime of m. This is an equivalence criterion; it proves neither "
                    + "RH nor finite 5040 closure.")),
                Paragraph(Text("For the converse, replace M by max(M,0). The full correction "
                    + "at every original record is bounded using fullC_leading at epsilon=1. "
                    + "For each real cutoff x, cutoff_record gives the least global optimizer "
                    + "with exactly that prime prefix, hence a genuine strict original record. "
                    + "The exact margin_identity and B_prefix yield a lower bound for "
                    + "D(Pn(x))*B(Pn(x)). normalization gives D(Pn(x))/D(x)>=1/2 "
                    + "on one tail. A fixed nonpositive lower constant can therefore be "
                    + "transferred to D(x)*B(x) without assuming an absolute bound on B.")),
                Paragraph(Text("Unconditional PNT ensures theta(x)>1 eventually. Log-log "
                    + "concavity gives log(log(theta(x)))-log(log(x))<=(theta(x)-x)/(x*log(x)). "
                    + "Use theta<=psi, the full complete_mertens_ledger and "
                    + "complete_mangoldt_le_neg_E3, with all Mangoldt prime powers retained, "
                    + "to obtain B(x)<=weightedTail(psiErrorKernel,x). Thus the original "
                    + "lower bound gives weightedTail>=-A/(sqrt(x)*log(x)) on one real tail.")),
                Paragraph(Text("WeightedTailInverse.tail_lower_bound applies using only "
                    + "the ledger's actual L1 kernel, with its closed-tail premise paid by "
                    + "one eventual threshold. It gives Q(x)>=-3*A/sqrt(x). The complete "
                    + "Chebyshev tail identity gives exactly Q(x)=-U(x)/x, so "
                    + "U(x)<=3*A*sqrt(x). At x=exp(y), the literal full arithmetic "
                    + "K(y) is at most 3*A+1 on one positive real tail, including the "
                    + "constant and complete trivial-zero corrections. Apply the parent "
                    + "IntegratedExplicit.actual_kernel_affine_tail_implies_rh with slope "
                    + "zero. No RH, chosen-zero, positivity or transform premise enters this direction.")),
                Paragraph(Text("The forward direction uses the accepted "
                    + "RHSharpOriginalRecordMargin.original_record_sharp_lower_endpoint "
                    + "at epsilon=1. Its RH premise is retained in this direction."))),
            DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Claim()
    {
        var m = F.Id("m");
        var n = F.Id("n");
        var price = F.Id("lambda");
        var t = F.Id("T");
        var p = Call("largestPrime", m);
        var record = All("n", Nat, Imp(Lt(D(0), n), Imp(Lt(n, m),
            Lt(Call("goldenResourceObjective", price, n), Call("goldenResourceObjective", price, m)))));
        var bound = Le(new Formula.Negate(F.Id("M")),
            Multiply(Call("D", p), Call("robinLogMargin", m)));
        var everyRecord = All("m", Nat, Imp(Le(D(2), m), All("lambda", Real,
            Imp(Lt(D(0), price), Imp(record, Imp(Le(t, p), bound))))));
        return Disp(new Formula.Logic(Ex("M", Real, Ex("T", Real,
            And(Le(D(2), t), everyRecord))), FormulaLogicOperator.Iff,
            Seq(Operatorname, Grp(F.Id("RiemannHypothesis")))));
    }
}
