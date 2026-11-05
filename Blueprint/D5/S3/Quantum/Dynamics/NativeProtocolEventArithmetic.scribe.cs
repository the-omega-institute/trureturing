using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;
internal sealed class NativeProtocolEventArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native event integrality and arithmetic resource bounds",
        H("Native event integrality and arithmetic resource bounds"),
        Blocks(Describe.Lean(DescribeId.Create("original-event-arithmetic"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolEventArithmetic.original_event_arithmetic"),
                H("Integral raw event masses exclude both reference-comparison values"),
                StatementSource.FromAuthor(ArithmeticStatement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/stewarttall2025algebraic")),
                Blocks(
                    Paragraph(Text("For every type L of terminal labels, every finite full-menu native tree T and every Boolean event e on its complete terminal path and terminal sixteen-bit word, the raw mass p=eventMass(T,e) is an algebraic integer over the ordinary integers. All fourteen actual gate addresses, deterministic feedback, complete diagonal zero-one measurements, zero outcomes, stops and expanded inverse calls are included. The input is the same fixed computational root Omega; no arbitrary input vector or external probability weights occur.")),
                    Paragraph(Text("The scalars t, beta and zeta of the actual matrices are algebraic integers: rational-angle exponential and cosine integrality give zeta and t, and beta squared equals t. Every number projection and bit flip has integer entries. Finite matrix addition, multiplication and powers therefore preserve entrywise integrality. Induction through the actual tree gives integral branch-matrix entries. Applying the fixed root, multiplying each amplitude by its physical complex conjugate and summing the selected raw events preserve integrality. The real event mass is reflected from its injective complex embedding. No success normalization is performed.")),
                    Paragraph(Text("Set q=(13-5 sqrt(5))/22 and w=(9 sqrt(5)-19)/22. In the existing quadratic golden field with generator phi, these are the images of coordinate pairs (9/11,-5/11) and (-14/11,9/11). Their field norms are respectively 1/11 and -1/11. Integrality would force an integer field norm; both rational values fail that condition. Consequently p differs from both q and w. This argument only needs absolute algebraic integrality of p and does not assert that p lies in the quadratic field.")),
                    Paragraph(Text("These exclusions apply directly to any original-record event formed by the stop-aware graft in NativeProtocolGraft. They do not establish that the actual chi preparation and its faithful-support Petz pullback have ideal masses q and w. Quadratic integer coordinates, the whole-tree nonphysical-conjugate estimate and the arithmetic factor-eleven bounds are supplied by NativeProtocolEventCoordinates and NativeProtocolEventArithmetic. The actual reference-state realization, original-record comparison and total-variation consumers remain separate obligations. Total Born-mass normalization and the equality of the ninth gate power with its inverse are not used or proved here."))),
                DescribeRole.Theorem), ResourceNode())));

    private static DocumentBlock ResourceNode() => Describe.Lean(
        DescribeId.Create("original-event-resource-bounds"),
        DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolEventArithmetic.original_event_resource_bounds"),
        H("Positive-event and factor-eleven arithmetic resource bounds"),
        StatementSource.FromAuthor(ResourceStatement()),
        AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/stewarttall2025algebraic")),
        Blocks(
            Paragraph(Text("The bounds apply to every actually computed eventMass of the same original tree T. K denotes kappa to twice Tree.maxCalls(T). Every positive raw event mass is at least one divided by K. For q=emptyTarget=(13-5 sqrt(5))/22 and w=referenceTarget=(9 sqrt(5)-19)/22, the two displayed discrepancy bounds use exactly the source constants and the same K. These are arithmetic bounds for raw masses, without conditioning or a probability-normalization premise.")),
            Paragraph(Text("For x=A+B tau the integer norm is A squared minus A B minus B squared, and the product of its two real evaluations equals that norm. Its nonvanishing is reused from the existing golden-integer norm theorem through the coordinate correspondence (A-B,B). For u=11q=(4,-5) and u=11w=(-5,9), the norms are 11 and minus 11. Direct expansion proves that the norm of 11x-u is divisible by 11. The existing original_event_arithmetic theorem supplies non-equality with q and w. Thus the nonzero norm has absolute value at least 11. The whole-tree conjugate bound and the triangle inequality give the stated denominators.")),
            Paragraph(Text("The arithmetic inequalities do not identify q or w as the ideal probabilities of the actual chi/Petz experiments. Their empty-prefix and five-call source-history realization, preservation of original records and failure zeros, graft resource identities and total-variation comparison still require the specified original-object consumers. The cut determinant and spectral clauses of V88 theorem 24.1 remain outside this event result."))),
        DescribeRole.Theorem);

    private static Formula ArithmeticStatement()
    {
        Formula L = F.Id("L"), T = F.Id("T"), e = F.Id("e");
        Formula p = Call("eventMass", T, e);
        Formula q = Seq(Frac, Grp(D(1,3), Minus, D(5), Sqrt, Grp(D(5))), Grp(D(2,2)));
        Formula w = Seq(Frac, Grp(D(9), Sqrt, Grp(D(5)), Minus, D(1,9)), Grp(D(2,2)));
        Formula neq(Formula a, Formula b) =>
            new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
        return Disp(All("L", Call("Type"), All("T", Call("Tree", L),
            All("e", Call("Events", T), And(Call("IsIntegral", Call("Int"), p),
                neq(p, q), neq(p, w))))));
    }

    private static Formula ResourceStatement()
    {
        Formula L=F.Id("L"), T=F.Id("T"), e=F.Id("e"), p=Call("eventMass",T,e);
        Formula K=Power(Call("kappa"),Seq(D(2),Star,Call("maxCalls",T)));
        Formula q=Call("emptyTarget"), w=Call("referenceTarget");
        Formula cq=Seq(Frac,Grp(D(1,3),Plus,D(5),Sqrt,Grp(D(5))),Grp(D(2,2)));
        Formula cw=Seq(Frac,Grp(D(1,9),Plus,D(9),Sqrt,Grp(D(5))),Grp(D(2,2)));
        Formula lower(Formula a,Formula c)=>Leq(Seq(Frac,Grp(D(1)),
            Grp(D(1,1),Star,Parenthesized(Seq(K,Plus,c)))),Call("abs",Seq(p,Minus,a)));
        Formula positive=new Formula.Logic(
            new Formula.Relation(D(0),FormulaRelationOperator.LessThan,p),
            FormulaLogicOperator.Implies,Leq(Power(K,Seq(Minus,D(1))),p));
        return Disp(All("L",Call("Type"),All("T",Call("Tree",L),All("e",Call("Events",T),
            And(Parenthesized(positive),lower(q,cq),lower(w,cw))))));
    }

    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);

    private static Formula Power(Formula a, Formula b) => Seq(Grp(Parenthesized(a)), Caret, Grp(b));

    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);

    private static Formula Rel(Formula a, Formula op, Formula b) =>
        Seq(Open, a, Sp, op, Sp, b, Close);

    private static Formula And(params Formula[] xs) =>
        xs.Aggregate((a,b) => Rel(a,Land,b));


}
