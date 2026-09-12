using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class PaddingGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Padding Gram entries are minimum-head multiplicities within each tail block.",
        H("The Gram Entries of Padding Residuals"),
        Blocks(
            Paragraph(Text(
                "Let A be a finite type with decidable equality and let h be a letter of A. "
                + "For a multiset b, tail(h,b) is the full multiset obtained by filtering out h; "
                + "count(h,b) is the number of occurrences of h, and tailCount(h,b) is the "
                + "number of all other letters, counted with multiplicity. The existing "
                + "headSlice(h,b,j) is replicate(j,h) + tail(h,b). "
                + "multiplicity(card(q),q) counts words with occupation q. "
                + "castR and castC are the natural-number inclusions into the real and "
                + "complex scalars. The subtraction j-1 in a head index is natural subtraction.")),
            T("last-tail-increments", "last_tail_mass_head_slice", "Consecutive multiplicity increments",
                General(All("h", A, All("b", Multi,
                    Imp(Lt(D(0), Call("tailCount", h, b)), All("j", N,
                        Eq(Call("lastTailMass", h, Slice(b, j)),
                            Call("if", Eq(j, D(0)), MR(Slice(b, D(0))),
                                Subtract(MR(Slice(b, j)), MR(Slice(b, Subtract(j, D(1)))))))))))),
                "For every natural j, the last-tail mass of the j-th head slice is its "
                + "multiplicity increment. At j=0 it is the initial multiplicity. "
                + "The sole positivity assumption is tailCount(h,b)>0; no ambient capacity "
                + "or positive head count is required. lastTailMass(h,q) is "
                + "tailCount(h,q) times multiplicity(card(q),q), divided by card(q), in the reals. "
                + "The head-removal multiplicity recurrence gives the difference formula."),
            Paragraph(Text(
                "For b<=a in multiset order, paddingResidual(h,a,b) is the existing vector "
                + "in Space(OccupationMemory(a,h)). A zero tail gives the sink basis vector. "
                + "A positive tail gives the sum, for 0<=j<=count(h,b), of the basis vector "
                + "at its actual tail and head index j, weighted by the complex inclusion of "
                + "sqrt(lastTailMass(h,headSlice(h,b,j))). InnerC is the complex inner product, "
                + "conjugate linear in the first argument and linear in the second.")),
            T("actual-padding-gram", "padding_residual_inner", "Whole-tail blocks and minimum head count",
                General(All("h", A, All("a", Multi, All("b", Multi, All("c", Multi,
                    Imp(And(Le(b, a), Le(c, a)),
                        Eq(Call("InnerC", Residual(b), Residual(c)),
                            Call("if", Eq(Call("tail", h, b), Call("tail", h, c)),
                                MC(Slice(b, Call("min", Call("count", h, b), Call("count", h, c)))),
                                D(0))))))))),
                "Different entire tails give inner product zero, even when their cardinalities "
                + "agree. Equal positive tails share precisely the head indices up to the smaller "
                + "head count. Orthonormality multiplies their real square-root weights, and the "
                + "finite sum of multiplicity increments gives the displayed entry. "
                + "If both tails are zero, both vectors are the sink and the pure-head "
                + "multiplicity is one. A sink and a positive-tail vector are orthogonal. "
                + "This includes empty occupations and zero head capacity. No maximal-head "
                + "or positive-head assumption is present."),
            Paragraph(Text(
                "residualScale(b) is the existing positive real sqrt(multiplicity(card(b),b)). "
                + "normalizedPadding(h,a,b) divides the actual padding residual by its complex inclusion. "
                + "smulC denotes complex scalar multiplication, inv is scalar inverse, castRC is "
                + "the real-to-complex inclusion, and sink(a,h) is basis(none) in the same "
                + "Space(OccupationMemory(a,h)). This is the actual terminal padding coordinate: "
                + "the existing physical memory embedding sends it to physicalFinal(a) for the "
                + "chosen maximal head. paddingMoment uses this sink in its second operand.")),
            T("normalized-padding", "normalizedPadding", "Actual normalized padding vectors",
                Actual(All("b", Multi, Eq(Phi(b), Call("smulC",
                    Call("inv", Call("castRC", Call("residualScale", b))), Residual(b))))),
                "The positive real scale fixes one coherent normalization, including phase."),
            T("padding-moment-definition", "paddingMoment", "Actual source moments",
                Actual(All("b", Multi, Eq(Z(b), Call("InnerC", Phi(b), Sink)))),
                "The first argument is conjugated. The common sink is the second argument."),
            T("normalized-padding-norm", "normalized_padding_norm", "Unit residual vectors",
                Actual(All("b", Multi, Imp(Le(b,a), Eq(Call("norm", Phi(b)),D(1))))),
                "The diagonal Gram entry is M(b); dividing by its positive square root gives norm one."),
            T("normalized-padding-tail-free", "normalized_padding_tail_free", "Pure-head vectors share the sink",
                Actual(All("b", Multi, Imp(And(Le(b,a), Eq(Call("tailCount",h,b),D(0))),
                    Eq(Phi(b),Sink)))),
                "A legal occupation with zero tail has multiplicity one and its actual vector is the sink."),
            T("normalized-padding-zero", "normalized_padding_zero", "The terminal vector",
                Actual(Eq(Phi(D(0)),Sink)),
                "The zero occupation always lies in the capacity box. Its normalized vector is the unit terminal sink."),
            T("padding-moment-values", "padding_moment", "Every source moment in its actual domain",
                Actual(All("b", Multi, Imp(Le(b,a), Eq(Z(b),
                    Call("if",Eq(Call("tailCount",h,b),D(0)),D(1),D(0)))))),
                "The ternary if(P,x,y) means x when P holds and y otherwise. Thus z(0)=1; "
                + "all nonzero moments off the head axis vanish. The positive-tail vector has no sink coordinate."),
            T("normalized-padding-axis", "normalized_padding_axis", "All legal head-axis vectors coincide",
                Actual(All("j",N,Imp(Le(j,Call("count",h,a)),
                    Eq(Phi(Call("replicate",j,h)),Sink)))),
                "This includes j=0 and every 1<=j<=count(h,a). In particular phi(0)=phi(e_h) "
                + "when count(h,a)>0; no positive-capacity hypothesis is needed for j=0."),
            T("padding-moment-axis", "padding_moment_axis", "Prescribed head-axis moments",
                Actual(All("j",N,Imp(Le(j,Call("count",h,a)),
                    Eq(Z(Call("replicate",j,h)),D(1))))),
                "All legal pure-head moments are exactly one. The statements hold for any head; "
                + "choosing a maximal head gives the axis required by the attainment source."))));

    private static Formula Phi(Formula q) => Call("normalizedPadding",h,a,q);
    private static Formula Z(Formula q) => Call("paddingMoment",h,a,q);
    private static Formula Sink => Call("sink",a,h);
    private static Formula Actual(Formula body) => General(All("h",A,All("a",Multi,body)));

    private const string Prefix = "D5/S3/Quantum/StationaryPreparation/PaddingGram.";
    private static DocumentBlock T(string id, string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            name is "normalizedPadding" or "paddingMoment" ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula Id(string name) => F.Id(name);
    private static Formula A => Id("A");
    private static Formula a => Id("a");
    private static Formula b => Id("b");
    private static Formula c => Id("c");
    private static Formula h => Id("h");
    private static Formula j => Id("j");
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula Multi => Call("Multiset", A);
    private static Formula Slice(Formula q, Formula k) => Call("headSlice", h, q, k);
    private static Formula MR(Formula q) => Call("castR", Call("multiplicity", Call("card", q), q));
    private static Formula MC(Formula q) => Call("castC", Call("multiplicity", Call("card", q), q));
    private static Formula Residual(Formula q) => Call("paddingResidual", h, a, q);
    private static Formula General(Formula body) => All("A", Id("Type"),
        Imp(And(Call("Fintype", A), Call("DecidableEq", A)), body));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
}
