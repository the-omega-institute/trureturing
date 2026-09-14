using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.InformationTemplateDebtStoreTests;

namespace StrataLint.Tests;

public sealed class InformationTemplateDebtWriterTests
{
    private static InformationTemplateUniverse Universe(InformationTemplateBindingState state)
    {
        var debt = Read();
        var occurrence = new InformationTemplateOccurrence(debt.Key, "Registration.lean", debt.StatementIdentity,
            debt.ContentInputs, state, state == InformationTemplateBindingState.DeclaredValidated ? new string('a', 64) : null,
            state == InformationTemplateBindingState.DeclaredUnresolved ? "IE-C050 reason=unclassified_form" : null,
            state == InformationTemplateBindingState.Undeclared ? null : "Binding.lean");
        return new(ImmutableDictionary<InformationOccurrenceKey, InformationTemplateOccurrence>.Empty.Add(debt.Key, occurrence),
            ImmutableHashSet.Create(debt.Key), ImmutableHashSet.Create("Registration.lean"), ImmutableHashSet.Create("Registration.lean"));
    }

    [Fact]
    public void immutable_base_seed_accepted()
    {
        var rows = InformationTemplateDebtWriter.Initialize(new(Seed, false), Seed,
            Snapshot(("Registration.lean", Source)), Universe(InformationTemplateBindingState.Undeclared));
        Assert.Equal(Row, System.Text.Encoding.UTF8.GetString(InformationTemplateDebtStore.WriteRow(Assert.Single(rows).Value).AsSpan()));
    }

    [Fact]
    public void seed_candidate_injection_rejected() =>
        Assert.Throws<FormatException>(() => InformationTemplateDebtWriter.Initialize(new(Seed, false),
            "a37c6134f47ae7f6faa9bf5d5cd0532b59c4d475", Snapshot(("Registration.lean", Source)),
            Universe(InformationTemplateBindingState.Undeclared)));

    [Fact]
    public void initialization_while_active_rejected() =>
        Assert.Throws<FormatException>(() => InformationTemplateDebtWriter.Initialize(new(Seed, true),
            Seed, Snapshot(("Registration.lean", Source)), Universe(InformationTemplateBindingState.Undeclared)));

    [Fact]
    public void seed_missing_base_input_rejected() =>
        Assert.Throws<FormatException>(() => InformationTemplateDebtWriter.Initialize(new(Seed, false),
            Seed, Snapshot(), Universe(InformationTemplateBindingState.Undeclared)));

    [Fact]
    public void writer_removes_exact_validated_row()
    {
        var row = Read();
        var debt = ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow>.Empty.Add(row.Key, row);
        Assert.Empty(InformationTemplateDebtWriter.Discharge(new(Seed, true), debt,
            Universe(InformationTemplateBindingState.DeclaredValidated)));
    }

    [Fact]
    public void writer_keeps_unresolved_row()
    {
        var row = Read();
        var debt = ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow>.Empty.Add(row.Key, row);
        Assert.Throws<FormatException>(() => InformationTemplateDebtWriter.Discharge(new(Seed, true), debt,
            Universe(InformationTemplateBindingState.DeclaredUnresolved)));
        Assert.Equal(row, Assert.Single(debt).Value);
    }

    [Fact]
    public void writer_keeps_undeclared_row()
    {
        var row = Read();
        var debt = ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow>.Empty.Add(row.Key, row);
        Assert.Equal(row, Assert.Single(InformationTemplateDebtWriter.Discharge(new(Seed, true), debt,
            Universe(InformationTemplateBindingState.Undeclared))).Value);
    }

    [Fact]
    public void writer_cannot_discharge_before_activation()
    {
        var row = Read();
        var debt = ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow>.Empty.Add(row.Key, row);
        Assert.Throws<FormatException>(() => InformationTemplateDebtWriter.Discharge(new(Seed, false), debt,
            Universe(InformationTemplateBindingState.DeclaredValidated)));
    }
}
