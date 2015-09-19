# -*- coding: utf-8 -*-

import json as J
import parser

class Example:
    def __init__(self,filename):
        json_data = Example._read_example_file(filename)
        self.matrix_A     = json_data.get("matrix_A")
        self.matrix_B_strict = json_data.get("matrix_B_strict")
        self.matrix_B_weak   = json_data.get("matrix_B_weak")
        self.comment      = json_data.get("comment")
        self.published_in = json_data.get("published_in")
        self.example_name = json_data.get("example_name")

    @staticmethod
    def _read_example_file(filename):
        with open(filename) as file_data:
            json_data=J.load(file_data)
            return json_data
