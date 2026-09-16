using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Monodromy;

internal sealed class TransvectionHistoryObservabilityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Monodromy/TransvectionHistoryObservability."
            + "history_kernel_eq_pairing_ball";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact agreement kernel of all bounded pulse histories is determined "
            + "by the rows reached in the actual directed pairing graph.",
        H("Exact Observation Kernels of Controlled Histories"),
        Blocks(
            Paragraph(Text(
                "Let K be any field, I a finite index type with decidable equality, "
                    + "and H any I-by-I matrix. Reuse the actual increment "
                    + "N_i=e_i H(i,*) and the Walk and Within definitions from "
                    + "TransvectionLieFiltration. The readout is ell_a(x)=H(a,*)x. "
                    + "A pulse is the actual vector transformation (1+N_i)x. "
                    + "The empty history acts as the identity, and history(i::w,x) "
                    + "applies pulse i after history(w,x). All pulse labels are available.")),
            Describe.Lean(
                DescribeId.Create("history-kernel-eq-pairing-ball"),
                DeclarationHandle.Create(Declaration),
                H("Bounded experimental histories identify exactly a directed graph ball"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural k and states x,y, their ell_a outputs "
                            + "agree after every pulse word of length at most k "
                            + "if and only if ell_j(x)=ell_j(y) for every j "
                            + "reachable from a by at most k nonzero entries of H. "
                            + "The formula writes equality of these two predicates. "
                            + "Neither skew symmetry nor nondegeneracy is assumed. "
                            + "The graph can be directed or disconnected and "
                            + "reachable rows may be zero or linearly dependent.")),
                    Paragraph(Text(
                        "Actual matrix multiplication gives ell_b(T_i z)="
                            + "ell_b(z)+H_bi ell_i(z). Comparing the two available "
                            + "histories w and i::w cancels the first term and, "
                            + "when H_bi is nonzero, transfers output agreement "
                            + "to sensor i with one less unit of history budget. "
                            + "Induction on directed walks proves the necessary "
                            + "coordinate equalities. An independent induction "
                            + "on actual pulse words proves sufficiency: every "
                            + "nonzero term extends the readout along an actual edge.")),
                    Paragraph(Text(
                        "The Lie-layer theorem is not used to infer this result. "
                            + "It concerns spans of matrix commutators, whereas "
                            + "the present theorem concerns state readouts after "
                            + "finite products of full pulse matrices. The only "
                            + "shared imported objects are the actual increments "
                            + "and pairing walks.")),
                    Paragraph(Text(
                        "For real nondegenerate alternating H, these pulses can "
                            + "be realized as unit-time flows of the quadratic "
                            + "Hamiltonians ell_i squared divided by two, with "
                            + "Poisson tensor -H-inverse. A quantum interpretation "
                            + "requires the canonical commutation relations and "
                            + "a compatible unitary representation. Those physical "
                            + "interpretations and the graph-ball commutator rank "
                            + "are separate ordinary mathematical deductions.")),
                    Paragraph(Text(
                        "The quantifier ranges over alternative control histories "
                            + "with separately prepared identical inputs. It does "
                            + "not describe noninvasive measurements along one run. "
                            + "For quantum states, the linear readouts concern "
                            + "first moments and do not determine arbitrary density "
                            + "operators. The theorem also presupposes a known H; "
                            + "unknown-Hamiltonian identification is a different problem."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Statement() => Disp(Seq(
        Forall, Sp, F.Id("H"), Comma, Sp, F.Id("a"), Comma, Sp,
        F.Id("k"), Comma, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        new Formula.Relation(
            Call("SameHistory", F.Id("H"), F.Id("a"), F.Id("k"), F.Id("x"), F.Id("y")),
            FormulaRelationOperator.Equal,
            Call("AgreementOnPairingBall", F.Id("H"), F.Id("a"), F.Id("k"),
                F.Id("x"), F.Id("y")))));
}
