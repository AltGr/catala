# This is a template file following the expected interface and declarations to
# implement the corresponding Catala module.
#
# You should replace all `raise Impossible` place-holders with your
# implementation and rename it to remove the ".template" suffix.

from catala_runtime import *
from typing import Any, List, Callable, Tuple
from enum import Enum


def sequence(begin:Integer, end:Integer):
    pos = (SourcePosition(filename="stdlib/list_internal.catala_en",
               start_line=4, start_column=13, end_line=4, end_column=21,
               law_headings=[]))
    raise Impossible(pos)
    return sequence__1

def nth_element_init():
    pos = (SourcePosition(filename="stdlib/list_internal.catala_en",
               start_line=9, start_column=13, end_line=9, end_column=24,
               law_headings=[]))
    raise Impossible(pos)
    return nth_element__1

nth_element = (nth_element_init())

def remove_nth_element_init():
    pos = (SourcePosition(filename="stdlib/list_internal.catala_en",
               start_line=14, start_column=13, end_line=14, end_column=31,
               law_headings=[]))
    raise Impossible(pos)
    return remove_nth_element__1

remove_nth_element = (remove_nth_element_init())
