using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class MersennePhaseThreeTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula d = F.Id("d"), j = F.Id("j"), i = F.Id("i");
        Formula length = Mul(Num(3), d), phase = Call("val", j);
        Formula seed = Mul(Sub(new Formula.Power(Num(2), d), Num(1)),
            Sub(new Formula.Power(Num(2), Add(d, Num(1))), Num(3)));
        Formula filter = F.Seq(i, F.InMacro, Call("Fin", length), F.Comma,
            Eq(new Formula.Modulo(Call("val", i), d), phase));
        Formula sum = F.Seq(new Formula.Subscript(F.Sum, filter),
            Call("actualSource", length, seed, i));
        Formula rhs = Mul(Call("modulus", length),
            Sub(new Formula.Subscript(Num(1), Eq(phase, Sub(d, Num(3)))),
                new Formula.Subscript(Num(1), Eq(phase, Sub(d, Num(1))))));
        Formula statement = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("d"), Name("Nat"),
            new Formula.Logic(new Formula.Relation(Num(3), FormulaRelationOperator.LessThanOrEqual, d),
                FormulaLogicOperator.Implies,
                new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("j"),
                    Call("Fin", d), Eq(sum, rhs))));
        return DocumentDefinition.Create(ScribeNode.Create(
        "The literal integer trace of each three-label physical phase is zero except for one positive and one negative full modulus, for every d at least three.",
        H("Three-point Mersenne phase traces"),
        Blocks(Describe.Lean(DescribeId.Create("actual-phase-trace"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Circle/MersennePhaseThreeTrace.actual_phase_trace"),
            H("The full physical phase filter"), StatementSource.FromAuthor(F.Disp(statement)),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Fix any natural d at least three and any j in Fin(d). Set B=2^d, g=B-1, q=B^2+B+1 and N=2^(3d)-1=gq. The indicator 1 with a predicate subscript is the integer one when that predicate holds and zero otherwise. The seed is the natural number (2^d-1)(2^(d+1)-3). The theorem sums SourceWidth.actualSource at every physical label i in Fin(3d) with i.val modulo d equal to j.val. The filter is exactly the three distinct original labels j, j+d and j+2d; numerical coincidences of source values never identify labels.")),
                Paragraph(Text("Put x=2^j, a=(2B-3)x, b=(5B+2)x and c=(3B+5)x, so a-b+c=0. Multiplication by B sends a to -b modulo q, and multiplication by B^2 sends a to c modulo q. The proof uses the existing SourceWidth.centered_unique, centered_bounds and centered_mod, together with explicit congruences and strict doubled bounds, to identify the centered representatives after scaling by g. It introduces no second centered uniqueness theorem.")),
                Paragraph(Text("There are four exhaustive branches. If j+4 is at most d, then 16x is at most B and the representatives modulo q are (a,-b,c), of sum zero. If j=d-3, then 8x=B and the representatives are (a,q-b,c), of sum q. If j=d-2, then 4x=B and the representatives are (a,q-b,c-q), of sum zero. If j=d-1, then 2x=B and the representatives are (a-q,2q-b,c-2q), of sum -q. Every triple satisfies the strict centered interval bounds; scaling gives the literal integer traces 0,+N,0,-N.")),
                Paragraph(Text("The only numerical premise is d at least three. The trace itself has no 19 premise, no coprimality or unit assumption, and no primality, least-period or upper-cutoff condition. In particular d=12 is included even when the arithmetic seed and modulus have an additional common factor 19. The statement remains an equality in the integers and is not replaced by congruence modulo N.")),
                Paragraph(Text("For the ongoing physical zero-algebra construction, this supplies the actual arithmetic phase values: ordinary phases contribute zero, while phases d-3 and d-1 contribute opposite full moduli. Later composition must retain the original labels and establish its own phase-union and cancellation arguments. This module proves no full subset classification, count, Boolean algebra, stabilizer theorem or infinite-family theorem. It makes no literature-novelty or full Circle claim; the supplied ordinary proof route and repository priors informed this same-family implementation."))),
            DescribeRole.Theorem)), []));
    }

    private static Formula Name(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Num(long n) => new Formula.Number(n);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
