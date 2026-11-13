using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Quantum.Approximate.SolovayKitaevNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Approximate;

internal sealed class SolovayKitaevRateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Approximate/SolovayKitaevRate.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scalar three-halves error recurrence and fivefold length growth yield the exact logarithmic exponent log(5)/log(3/2).",
        H("Solovay–Kitaev error and level estimates"),Blocks(
            Paragraph(Text("These scalar and logarithmic proofs are Apache-2.0 reuse from Zayn Blore's CSD SolovayKitaevStep and SolovayKitaevCount at commit 9b2d2c17e926ae13795119c5f2f62e85ea240c2d. Their exact original file and declaration references appear in the Lean source. The full license is docs/reports/qmutualinfo/csd-lean4-LICENSE.txt. They bound scalar sequences and level counts; the ordinary-word theorem separately supplies one actual list satisfying error and length together.")),
            Entry("scalar-error-closure","skError_le_rpow","Closed scalar error bound",ErrorClosure(),
                "For a nonnegative error sequence with e(n+1)<=C*e(n)^(3/2), induction gives double exponential decay after multiplication by C^2. C is any positive real constant."),
            Entry("step-estimate","step_bound","The sufficient three-halves step",StepBound(),
                "At a=sqrt(2)*sqrt(epsilon)+epsilon and delta=epsilon, the commutator stability expression is at most 33*epsilon^(3/2) whenever sqrt(epsilon)<=1/2."),
            Entry("level-reaches-error","skLevel_rpow_le","The chosen level reaches the error",LevelError(),
                "For 0<epsilon<=b<1, skLevel(b,epsilon)=ceil(log(log(epsilon)/log(b))/log(3/2)). At this level the closed error is at most epsilon."),
            Entry("level-fivefold-cost","five_pow_skLevel_le","Fivefold growth is polylogarithmic",LevelLength(),
                "Rounding the level upward costs a factor of at most five. The exponent is exactly log(5)/log(3/2); this scalar estimate asserts no word-length bound without a paired word construction."))));
    private static ScribeNode Entry(string id,string name,string title,Formula formula,string body) =>
        Describe.Lean(DescribeId.Create(id),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(formula),AssessedProvenance.FromLiterature("dawsonnielsen2006solovaykitaev"),
            Blocks(Paragraph(Text(body))),DescribeRole.Theorem);
    private static Formula ErrorClosure()
    {
        Formula c=X("C"),e=X("e"),n=X("n"),j=X("j");
        Formula nonneg=All("j",Call("Nat"),Le(N(0),At(e,j)));
        Formula rec=All("j",Call("Nat"),Le(At(e,Add(j,N(1))),Multiply(c,Pow(At(e,j),Frac(N(3),N(2))))));
        Formula result=All("n",Call("Nat"),Le(Multiply(Pow(c,N(2)),At(e,n)),
            Pow(Multiply(Pow(c,N(2)),At(e,N(0))),Pow(Frac(N(3),N(2)),n))));
        return All("C",Call("Real"),All("e",new Formula.TypeArrow(Call("Nat"),Call("Real")),
            Imp(And(Pos(c),And(nonneg,rec)),result)));
    }
    private static Formula StepBound()
    {
        Formula e=X("epsilon"),a=Add(Multiply(Call("sqrt",N(2)),Call("sqrt",e)),e);
        Formula result=Le(Multiply(Multiply(Multiply(N(4),a),e),Add(N(1),a)),Multiply(N(33),Pow(e,Frac(N(3),N(2)))));
        return All("epsilon",Call("Real"),Imp(And(Le(N(0),e),Le(Call("sqrt",e),Frac(N(1),N(2)))),result));
    }
    private static Formula Level(Formula body) => All("b",Call("Real"),All("epsilon",Call("Real"),
        Imp(And(Pos(X("b")),And(Lt(X("b"),N(1)),And(Pos(X("epsilon")),Le(X("epsilon"),X("b"))))),body)));
    private static Formula LevelError() => Level(Le(Pow(X("b"),Pow(Frac(N(3),N(2)),
        Call("skLevel",X("b"),X("epsilon")))),X("epsilon")));
    private static Formula LevelLength() => Level(Le(Pow(N(5),Call("skLevel",X("b"),X("epsilon"))),
        Multiply(N(5),Pow(Frac(Call("log",X("epsilon")),Call("log",X("b"))),Exponent()))));
}
