'''
Created on 13.03.2014

Provides functionality for visualizing the synthesized system
'''
import os

from thirdparty.pydot import pydot
import helpers.io


def model_to_dot(template_model_dict, target_path, name=None):
    '''
    Generates dot file for a given set of template models
    :param template_model_dict: template_index to template model dictionary
    :param target_path: Solution file path
    :param name: Optional problem name (default: specification file name
                 without extension)
    '''
    if name is None:
        name = os.path.splitext(os.path.basename(target_path))[0]

    graph = pydot.Dot("solution", graph_type='digraph')
    for template_index, model in template_model_dict.items():
        subgraph = pydot.Subgraph('clusterTemplate_%d' %
                                  template_index, rank='same',
                                  label='T%d' % template_index, color='blue')
        graph.add_subgraph(subgraph)
        for state in model.states:
            subgraph.add_node(
                pydot.Node(state, label=_format_node_label(state,
                                                           model.outputs)))
        for src_state, (input_signals, guard_set), \
                dst_state in model.transitions_list:
            subgraph.add_edge(
                pydot.Edge(src_state, dst_state,
                           label=_format_transition_label(input_signals,
                                                          guard_set)))

    helpers.io.mkdir_p(os.path.dirname(target_path))
    return graph.write(target_path)


def _format_node_label(state, outputs):
    '''
    Returns a node label string that contains state name and
    output label assignments
    :param state:
    :param outputs:
    '''
    output_values = [output_name if output_dict[state] else ("/" + output_name)
                     for output_name, output_dict in outputs.items()]
    out_label = ",".join(output_values)
    return "%s\n %s" % (state, out_label)


def _format_transition_label(input_signal_value_tuples, guard_set):
    '''
    Returns a transition label string

    :param input_signal_value_tuples: input signals and required values
           s.t. transition is enabled
    :param guard_set: guard set for the given transition
    '''
    signal_part = ','.join([("%s" if val else "!%s") %
                            sig.name for sig, val in
                            input_signal_value_tuples])
    return '%s\n%s' % (signal_part, guard_set)
