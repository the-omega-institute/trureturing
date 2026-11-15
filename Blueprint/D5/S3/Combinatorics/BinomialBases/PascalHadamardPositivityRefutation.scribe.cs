using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal sealed class PascalHadamardPositivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/vsp2026pascalhadamard");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strictly separated Pascal minor has negative determinant at real exponent one tenth, refuting the original MO515594 positivity assertion.",
        H("A negative minor of a fractional Hadamard power of the Pascal matrix"),
        Blocks(
            Describe.Lean(DescribeId.Create("pascal-hadamard-positivity-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The full original strict-positivity assertion"),
                StatementSource.FromAuthor(Disp(Iff(V("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("VSP's original question, MathOverflow 515594, revision 1, GUID 24043C19-8B17-4527-819F-D0DAEA1E8F86. Both n and k range over all natural numbers. The functions alpha and beta list row and column indices in their original increasing order, with every index at most n. The condition beta(j)<alpha(i) for every pair imposes strict separation of the complete column list from the complete row list.")),
                    Paragraph(Text("Nat.choose gives the actual entries of the finite Pascal matrix indexed by 0,...,n. Casting these natural entries to the reals and using real rpow gives its Hadamard power; Matrix.of on the two Fin(k) indices is exactly the selected square submatrix, and Matrix.det is its ordinary determinant. For k>0, the displayed pairwise conditions are equivalent to beta(0)<...<beta(k-1)<alpha(0)<...<alpha(k-1). For k=0, all index conditions are vacuous and the empty determinant is one, so including the empty minor adds a true case.")),
                    Paragraph(Text("The source question is attributed to VSP at https://mathoverflow.net/questions/515594 under https://creativecommons.org/licenses/by-sa/4.0/. This adaptation replaces the source's one-based lists by Fin(k) functions and makes every natural-index bound explicit. The separately appended nonvanishing question for r>1 is not part of this assertion."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascal-hadamard-positivity-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The original assertion is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Take n=5, k=3, alpha=(3,4,5), beta=(0,1,2) and r=1/10. The strict ordering is 0<1<2<3<4<5. The selected unpowered matrix has rows (1,3,3), (1,4,6), (1,5,10). Matrix.det_fin_three and Real.mul_rpow identify the powered determinant D with 40^(1/10)+18^(1/10)+15^(1/10)-2*30^(1/10)-12^(1/10). All roots here are real rpow on positive bases.")),
                    Paragraph(Text("Put q=1000000. Exact integer inequalities give 40*q^10<1446126^10, 18*q^10<1335142^10, 15*q^10<1311020^10, 1405115^10<30*q^10 and 1282088^10<12*q^10. Nonnegativity, the identity (a^(1/10))^10=a and strict monotonicity of tenth powers give upper bounds for the three positive terms and lower bounds for the two negative terms. Thus D<(1446126+1335142+1311020-2*1405115-1282088)/q=-30/1000000<0. The proof uses exact rational arithmetic and the standard real-power identities, with no floating-point premise.")),
                    Paragraph(Text("This one admissible negative minor disproves the full original universal assertion; no restriction on its other indices or exponents is needed. General failures of fractional Hadamard powers are known, and the bounded inspected sources did not identify a prior complete answer for this fixed Pascal-family question. Worldwide priority remains unknown. This argument gives no conclusion about the later all-size nonvanishing question for r>1."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mo515594-original-pascal-hadamard-positivity"),
                    ResolutionKind.Refuted)))));

    private static Formula ClaimBody()
    {
        var n = V("n"); var k = V("k"); var r = V("r"); var i = V("i"); var j = V("j");
        var index = Call("Fin", k);
        Formula At(string name, Formula x) => Apply(V(name), x);
        Formula Increasing(string name) => All("i", index, All("j", index,
            Imp(Lt(i, j), Lt(At(name, i), At(name, j)))));
        Formula Bounded(string name) => All("i", index, Le(At(name, i), n));
        var separated = All("i", index, All("j", index, Lt(At("beta", j), At("alpha", i))));
        var binomial = Apply(Q("Nat", "choose"), At("alpha", i), At("beta", j));
        var entry = new Formula.Power(Typed(Typed(binomial, Nat()), Real()), r);
        var matrix = Apply(Q("Matrix", "of"), LambdaOf("i", index, LambdaOf("j", index, entry)));
        var positive = Lt(D(0), Apply(Q("Matrix", "det"), matrix));
        var body = Imp(Lt(D(0), r), Imp(Increasing("alpha"), Imp(Increasing("beta"),
            Imp(Bounded("alpha"), Imp(Bounded("beta"), Imp(separated, positive))))));
        return All("n", Nat(), All("k", Nat(),
            All("alpha", new Formula.TypeArrow(index, Nat()),
            All("beta", new Formula.TypeArrow(index, Nat()), All("r", Real(), body)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(Formula x, Formula type) => Par(Seq(x, Colon, Sp, type));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Par(body));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Iff, Par(y));
}
