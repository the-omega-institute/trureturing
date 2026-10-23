using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class NestedMexStabilizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary finite compositions of a nested minimum-excluded-value map stabilize after two applications.",
        H("Stabilization of Nested Mex Maps"),
        Blocks(
            Paragraph(Text(
                "Let E1, E2, E3 and K be finite subsets of the natural numbers, each containing zero. "
                + "For an input x put a=mex(E1 union {x}), v=mex(K union {a}), "
                + "b=mex(E2 union {a,v}), and M(x)=mex(E3 union {a,b}). "
                + "A list is composed in application order, with its first entry acting first.")),
            Describe.Lean(
                DescribeId.Create("nested-mex-composition-stabilization"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Games/NestedMexStabilization.result"),
                H("Every positive input stabilizes after two compositions"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write alpha=mex(E1) and beta=mex(E1 union {alpha}); alpha is positive and beta exceeds alpha. "
                    + "The first mex is beta only at alpha and is alpha elsewhere, so M has at most two values. "
                    + "The two intervening v values either coincide below alpha or are both at least alpha. "
                    + "Their middle sets therefore agree below alpha, as do the final sets. "
                    + "Distinct final values are at least alpha, and only the exceptional value can equal alpha. "
                    + "Consequently, for 0<r<s with distinct outputs, the output minimum is at least r; "
                    + "equality fixes r. This property is preserved through every component, excluding a swap. "
                    + "The resulting map has at most two image values and no positive two-cycle, which gives R cubed equal to R squared."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Tyagi, arXiv:2610.06925v1, equations (1), (2) and (21), uses removals d dividing every other heap. "
                + "Let A be any nonempty multiset of positive fixed heaps with gcd(A)=4, H at least its maximum, "
                + "T=2 lcm(1,...,H), and f(n)=g(A+{n}). Assume that every actual nonempty direct fixed follower Q "
                + "has an eventual T tail for g(Q+{n}). These are all legal fixed moves, including removals that do not divide the selected heap. "
                + "Beyond a common threshold B at least 5, 2 min(A)+1 and every follower start, "
                + "the finite fixed-follower coefficient F(n) repeats after T, and "
                + "f(n)=mex(F(n) union {f(n-1),f(n-2),f(n-4)}). "
                + "Empty fixed followers contribute singleton values above the parent bound and can be omitted.")),
            Paragraph(Text(
                "Let c count fixed heaps of valuation exactly two, and set z0=0 for even c and z0=4 for odd c. "
                + "The actual outcome criterion makes precisely the z0 residue modulo eight zero. "
                + "At a zero anchor z write p=f(z-3), x=f(z-2), q=f(z-1), "
                + "u=mex{0,p,q}, a=f(z+2), v=f(z+3), b=f(z+4), w=f(z+5), y=f(z+6), t=f(z+7). "
                + "Then E1=F(z+2) union {0,u}, K={0,u,q}, E2=F(z+4) union {0}, "
                + "and E3=F(z+6) union {w} give exactly M(x)=y; E3 contains zero by the actual outcome law at z+6. "
                + "The intervening odd value v is recomputed inside M.")),
            Paragraph(Text(
                "The two actual tails at z0+5 and z0+7 modulo eight remain additional hypotheses. "
                + "They repeat p,q,w,t and hence the coefficient sets after T. For k=T/8 the actual seeds obey "
                + "x(j+1)=M(j)(x(j)) with M(j+k)=M(j). The theorem stabilizes the k-step composition. "
                + "Starting at the first zero anchor z at least max(B,O+3), where O is the start of those two tails, "
                + "the full T tail follows from z+2T, at most max(B,O+3)+7+2T. "
                + "This embeds the actual trajectory only: arbitrary seeds can violate the remaining odd equations for w or t. "
                + "Neither the two residue tails nor equation (21) is proved here."))),
        []));

    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. xs]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula ResultFormula()
    {
        var l = F.Id("L");
        var x = F.Id("x");
        var once = Call("run", l, x);
        var twice = Call("run", l, once);
        var thrice = Call("run", l, twice);
        var nonempty = new Formula.Relation(l, FormulaRelationOperator.NotEqual,
            Seq(OpenBracket, CloseBracket));
        var positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, x);
        var conclusion = new Formula.Relation(thrice, FormulaRelationOperator.Equal, twice);
        return Disp(All("L", Call("List", F.Id("Coefficients")), Imp(nonempty,
            All("x", F.Id("Nat"), Imp(positive, conclusion)))));
    }
}
